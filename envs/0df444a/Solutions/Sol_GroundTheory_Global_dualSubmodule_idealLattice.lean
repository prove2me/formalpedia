-- Prove2me | solution 1 for GroundTheory.Global.dualSubmodule_idealLattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:35:50.121821+00:00
-- url     : https://prove2.me/submissions/9f72dd5a-46d4-4617-8cf6-42968e37cc40

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceFourier
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceDualLattice
import Theorems.Thm_GroundTheory_Global_coeToSubmodule_traceDualIdeal
import Theorems.Thm_GroundTheory_Global_mixedTraceForm_mixedEmbedding
import Theorems.Thm_GroundTheory_Global_mixedTraceForm_nondegenerate


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
open scoped Classical ENNReal nonZeroDivisors
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
namespace GroundTheory.Global
theorem _root_.solution (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (mixedTraceForm K).dualSubmodule (idealLattice K I) = idealLattice K (traceDualIdeal K I) := by
  set b := basisOfFractionalIdeal K I
  have hdual : (mixedTraceForm K).dualBasis (mixedTraceForm_nondegenerate K)
      (fractionalIdealLatticeBasis K I) = fun i => mixedEmbedding K (b.traceDual i) := by
    rw [LinearMap.BilinForm.dualBasis_eq_iff]
    intro i j
    rw [fractionalIdealLatticeBasis_apply, mixedTraceForm_mixedEmbedding,
      Module.Basis.trace_traceDual_mul]
    split_ifs <;> simp
  have hspan : (Submodule.traceDual ℤ ℚ (I : Submodule (𝓞 K) K)).restrictScalars ℤ =
      Submodule.span ℤ (Set.range b.traceDual) :=
    Submodule.traceDual_span_of_basis ℤ (I : Submodule (𝓞 K) K) b (by
      ext x
      rw [Submodule.restrictScalars_mem, mem_span_basisOfFractionalIdeal]
      rfl)
  ext y
  rw [← span_idealLatticeBasis, LinearMap.BilinForm.dualSubmodule_span_of_basis _
    (mixedTraceForm_nondegenerate K), hdual, mem_idealLattice,
    show Set.range (fun i => mixedEmbedding K (b.traceDual i)) =
      (mixedEmbedding K).toIntAlgHom.toLinearMap '' Set.range b.traceDual by
        rw [← Set.range_comp]; rfl,
    ← Submodule.map_span, Submodule.mem_map, ← hspan]
  simp only [Submodule.restrictScalars_mem, ← coeToSubmodule_traceDualIdeal]
  rfl
end GroundTheory.Global
