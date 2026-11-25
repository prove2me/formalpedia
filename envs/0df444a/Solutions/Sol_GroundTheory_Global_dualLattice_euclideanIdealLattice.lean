-- Prove2me | solution 1 for GroundTheory.Global.dualLattice_euclideanIdealLattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:54:25.548883+00:00
-- url     : https://prove2.me/submissions/b77d21fa-bdf5-4220-84bd-8d69b0be4ca8

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceDualLattice
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LatticePoissonBasic
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceLatticeEuclidean
import Theorems.Thm_GroundTheory_Global_mem_euclideanIdealLattice
import Theorems.Thm_GroundTheory_Global_mem_euclideanConjIdealLattice
import Theorems.Thm_GroundTheory_Global_mem_dualLattice
import Theorems.Thm_GroundTheory_Global_mem_idealLattice_traceDualIdeal_iff
import Theorems.Thm_GroundTheory_Global_mixedTraceForm_comm
import Theorems.Thm_GroundTheory_Global_mixedTraceForm_eq_inner


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module MeasureTheory
open scoped Classical RealInnerProductSpace nonZeroDivisors
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
namespace GroundTheory.Global
theorem _root_.solution (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    dualLattice (euclideanIdealLattice K I) =
      euclideanConjIdealLattice K (traceDualIdeal K I) := by
  ext μ
  rw [mem_dualLattice, mem_euclideanConjIdealLattice, mem_idealLattice_traceDualIdeal_iff]
  constructor
  · intro h x hx
    obtain ⟨k, hk⟩ := h (mixedToEuclidean K x) (by
      rw [mem_euclideanIdealLattice, ContinuousLinearEquiv.symm_apply_apply]
      exact hx)
    refine ⟨k, ?_⟩
    rw [mixedTraceForm_comm, mixedTraceForm_eq_inner, ContinuousLinearEquiv.apply_symm_apply,
      real_inner_comm]
    exact hk
  · intro h ℓ hℓ
    obtain ⟨k, hk⟩ := h ((mixedToEuclidean K).symm ℓ) hℓ
    refine ⟨k, ?_⟩
    rw [← hk, mixedTraceForm_comm, mixedTraceForm_eq_inner, ContinuousLinearEquiv.apply_symm_apply,
      ContinuousLinearEquiv.apply_symm_apply, real_inner_comm]
end GroundTheory.Global
