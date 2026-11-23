-- Prove2me | solution 1 for GroundTheory.Automorphic.exists_borel_of_isUpperTriangular
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:39:40.364643+00:00
-- url     : https://prove2.me/submissions/03de1e5c-7024-4f6c-9e7e-03c116331310

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Matrix DoubleCoset
variable {n : ℕ} {k : Type*} [Field k]
namespace GroundTheory.Automorphic
theorem _root_.solution (M : Matrix (Fin n) (Fin n) k)
    (hM : M.IsUpperTriangular) (hd : ∀ i, M i i ≠ 0) :
    ∃ b ∈ borel n k, (b : Matrix (Fin n) (Fin n) k) = M := by
  have hdet : IsUnit M := by
    rw [Matrix.isUnit_iff_isUnit_det, det_of_isUpperTriangular hM, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hd i
  obtain ⟨u, hu⟩ := hdet
  refine ⟨u, ?_, hu⟩
  show (u : Matrix (Fin n) (Fin n) k).IsUpperTriangular
  rw [hu]
  exact hM
end GroundTheory.Automorphic
