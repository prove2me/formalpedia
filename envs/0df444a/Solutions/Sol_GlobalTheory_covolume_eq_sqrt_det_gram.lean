-- Prove2me | solution 1 for GlobalTheory.covolume_eq_sqrt_det_gram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:44:56.74149+00:00
-- url     : https://prove2.me/submissions/32c93540-7cfb-45d3-89d3-478732a6186b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LinearIndependentRealOfIntOfDiscrete
import Theorems.Thm_GlobalTheory_covolume_span_basis_eq_sqrt_det_gram

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexOrder InnerProductSpace MatrixOrder
open Module Submodule MeasureTheory Matrix
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι]
variable [MeasurableSpace E] [BorelSpace E]
namespace GlobalTheory
theorem _root_.solution [DecidableEq ι] (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] (b : Basis ι ℤ L) :
    ZLattice.covolume L = √(gram ℝ fun i ↦ (b i : E)).det := by
  have h := covolume_span_basis_eq_sqrt_det_gram (b.ofZLatticeBasis ℝ L)
  rw [b.ofZLatticeBasis_span ℝ] at h
  rw [h]
  congr 3
  ext i
  simp
end GlobalTheory
