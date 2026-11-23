-- Prove2me | solution 1 for GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingEquiv_tmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:57:07.165598+00:00
-- url     : https://prove2.me/submissions/3e4e81ed-76fa-4231-84a5-38f8a3241caf

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Infinite
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_InfiniteAdele

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Global
open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped NumberField.LiesOver TensorProduct
open GroundTheory.Global.InfinitePlace
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable [NumberField K] [NumberField L]
namespace GroundTheory.Global.InfinitePlace
theorem _root_.solution (l : L) (x : InfiniteAdeleRing K)
    (w : InfinitePlace L) :
    tensorInfiniteAdeleRingEquiv (l ⊗ₜ x) w =
      (l : w.Completion) * algebraMap (w.comap (algebraMap K L)).Completion w.Completion
        (x (w.comap (algebraMap K L))) := by
  change tensorPiEquivLeft (L := L) (w.comap (algebraMap K L))
    (l ⊗ₜ x (w.comap (algebraMap K L))) ⟨w, liesOver_comap w⟩ = _
  rw [tensorPiEquivLeft_tmul]
end GroundTheory.Global.InfinitePlace
