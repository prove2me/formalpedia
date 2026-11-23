-- Prove2me | solution 1 for GlobalTheory.MonoDeg.sum_eq_sum_finsuppAntidiag
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:41:33.668897+00:00
-- url     : https://prove2.me/submissions/97a974f7-d82f-47b8-b4dc-ef194fe8f844

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasiRegularSeqSelfIffLocalizationMaximal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
namespace GlobalTheory
namespace MonoDeg
theorem _root_.solution {ι N : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommMonoid N] (a : ℕ) (g : (ι →₀ ℕ) → N) :
    ∑ α : MonoDeg ι a, g α.1 = ∑ α ∈ Finset.finsuppAntidiag Finset.univ a, g α := by
  symm
  refine Finset.sum_subtype _ (fun α => ?_) g
  simp [Finsupp.degree_eq_sum]
end MonoDeg
end GlobalTheory
