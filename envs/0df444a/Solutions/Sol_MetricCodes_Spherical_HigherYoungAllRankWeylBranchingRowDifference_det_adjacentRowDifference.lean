-- Prove2me | solution 1 for MetricCodes.Spherical.HigherYoungAllRankWeylBranchingRowDifference.det_adjacentRowDifference
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:44.102863+00:00
-- url     : https://prove2.me/submissions/02d919cb-b3ea-4098-9a8a-e60087e71ec2

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option autoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option autoImplicit false
set_option maxHeartbeats 1800000
open MetricCodes
open MetricCodes.Spherical
set_option autoImplicit false
open MetricCodes.Spherical.HigherYoungAllRankWeylBranchingRowDifference
namespace MetricCodes.Spherical.HigherYoungAllRankWeylBranchingRowDifference
theorem _root_.solution {R : Type*} [CommRing R] {r : ℕ}
    (M : Matrix (Fin (r + 1)) (Fin (r + 1)) R) :
    (adjacentRowDifference M).det = M.det := by
  let e : Equiv.Perm (Fin (r + 1)) := Fin.revPerm
  have hdet : (M.submatrix e e).det =
      ((adjacentRowDifference M).submatrix e e).det := by
    apply Matrix.det_eq_of_forall_row_eq_smul_add_pred
      (fun _ : Fin r => (1 : R))
    · intro j
      simp [adjacentRowDifference, e]
    · intro i j
      change M (Fin.rev i.succ) (Fin.rev j) =
        adjacentRowDifference M (Fin.rev i.succ) (Fin.rev j) +
          1 * M (Fin.rev i.castSucc) (Fin.rev j)
      rw [Fin.rev_succ, Fin.rev_castSucc]
      simp [adjacentRowDifference]
  simpa [e] using hdet.symm
end MetricCodes.Spherical.HigherYoungAllRankWeylBranchingRowDifference
