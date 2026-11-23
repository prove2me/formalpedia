-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisLevi.factor
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:37:26.320537+00:00
-- url     : https://prove2.me/submissions/dc2a5e0f-52f0-4b9b-8d3f-5fa05627a8ef

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LeviDecompOfBlockDet
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLevi_piQ_jQ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisLevi
variable {E R : Type} [Field E] [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.RgEisLevi
theorem _root_.solution (A : Ad E R) (ε : ℤˣ) (h : ∀ x, A.σ (A.σ x) = x) (q : A.uQ ε (Set.univ : Set ι)) (p k : GL ι R)
    (e : piQ A ε q = p * k) : ∃ q' : A.uQ ε (Set.univ : Set ι), piQ A ε q' = p ∧ q.1 = q'.1 * (jQ A ε h k).1 := by
  refine ⟨q * (jQ A ε h k)⁻¹, ?_, ?_⟩
  · rw [map_mul, map_inv, piQ_jQ, e, mul_inv_cancel_right]
  · rw [← Subgroup.coe_mul, inv_mul_cancel_right]
end GlobalTheory.CompanionTheory.RgEisLevi
