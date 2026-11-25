-- Prove2me | solution 1 for GroundTheory.PAdicHodge.isClosed_image_coe_of_finiteDimensional
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:18:10.839966+00:00
-- url     : https://prove2.me/submissions/214d35cc-02c5-440c-88a3-c4d2a775321a

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma

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
open Polynomial
noncomputable section
open UniformSpace Topology
variable {p : ℕ} [hp : Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
namespace GroundTheory.PAdicHodge
theorem _root_.solution [FiniteDimensional ℚ_[p] K] :
    IsClosed (((↑) : PadicAlgCl p → ℂ_[p]) '' (K : Set (PadicAlgCl p))) := by
  have : FiniteDimensional ℚ_[p] (Subalgebra.toSubmodule K.toSubalgebra) :=
    ‹FiniteDimensional ℚ_[p] K›
  have hK : IsComplete (K : Set (PadicAlgCl p)) :=
    (Subalgebra.toSubmodule K.toSubalgebra).complete_of_finiteDimensional
  exact ((isComplete_image_iff (Completion.isUniformInducing_coe (PadicAlgCl p))).2 hK).isClosed
end GroundTheory.PAdicHodge
