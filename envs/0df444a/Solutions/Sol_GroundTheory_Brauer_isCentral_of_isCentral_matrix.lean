-- Prove2me | solution 1 for GroundTheory.Brauer.isCentral_of_isCentral_matrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:05:11.745801+00:00
-- url     : https://prove2.me/submissions/de54c16c-e4f4-4f3a-b860-94541cbdce0b

import Mathlib
import Definitions.Def_GroundTheory_Brauer_TensorSimple
import Definitions.Def_GroundTheory_Brauer_IsBrauerEquivalentIffNonemptyAlgEquiv
import Theorems.Thm_GroundTheory_Brauer_tensorCSA_carrier
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Brauer.tensorCSA_carrier



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Brauer
open TensorProduct
universe u v w
variable {K : Type u} [Field K]
namespace GroundTheory.Brauer
theorem _root_.solution {D : Type w} [Ring D] [Algebra K D] {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι] [Algebra.IsCentral K (Matrix ι ι D)] :
    Algebra.IsCentral K D where
  out z hz := by
    have hs : Matrix.scalar ι z ∈ Subalgebra.center K (Matrix ι ι D) := by
      rw [Subalgebra.mem_center_iff] at hz ⊢
      intro M
      ext i j
      simp [hz]
    obtain ⟨k, hk⟩ := Algebra.mem_bot.mp (Algebra.IsCentral.out hs)
    refine Algebra.mem_bot.mpr ⟨k, ?_⟩
    have := congrFun (congrFun hk (Classical.arbitrary ι)) (Classical.arbitrary ι)
    simpa [Matrix.algebraMap_matrix_apply] using this
end GroundTheory.Brauer
