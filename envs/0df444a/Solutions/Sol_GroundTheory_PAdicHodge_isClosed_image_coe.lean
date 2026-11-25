-- Prove2me | solution 1 for GroundTheory.PAdicHodge.isClosed_image_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:18:09.355404+00:00
-- url     : https://prove2.me/submissions/9ac7c28d-965d-4e74-b922-7b141519d224

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTraceClosure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open UniformSpace Topology Filter Set
noncomputable section
variable {p : ℕ} [Fact p.Prime]
variable (E : IntermediateField ℚ_[p] (PadicAlgCl p))
variable (R : PadicAlgCl p → PadicAlgCl p)
variable {E R}
namespace GroundTheory.PAdicHodge
theorem _root_.solution (k : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] k] :
    IsClosed (((↑) : PadicAlgCl p → ℂ_[p]) '' (k : Set (PadicAlgCl p))) := by
  have : FiniteDimensional ℚ_[p] (Subalgebra.toSubmodule k.toSubalgebra) :=
    ‹FiniteDimensional ℚ_[p] k›
  have hc : IsComplete (k : Set (PadicAlgCl p)) :=
    Submodule.complete_of_finiteDimensional (Subalgebra.toSubmodule k.toSubalgebra)
  exact ((UniformSpace.Completion.isUniformEmbedding_coe
    (PadicAlgCl p)).isUniformInducing.isComplete_iff.2 hc).isClosed
end GroundTheory.PAdicHodge
