-- Prove2me | solution 1 for MetricCodes.Boolean.hammingAdjacentChannel_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.702855+00:00
-- url     : https://prove2.me/submissions/ba0b8cae-e403-4e5b-bd11-f33f41406802

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Boolean_deleteChannel_orthogonal_addChannel

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
open scoped BigOperators Matrix
open MetricCodes.Boolean
variable {n : ℕ}
namespace MetricCodes.Boolean
theorem _root_.solution
    (n k L : ℕ)
    (target source other : Fin (L - k + 1))
    (hne : source ≠ other)
    (f g : Function n) :
    coordinateDot
      (hammingAdjacentChannel n k L target source f)
      (hammingAdjacentChannel n k L target other g) = 0 := by
  classical
  have hvalne : source.val ≠ other.val := by
    intro h
    exact hne (Fin.ext h)
  have hvalne' : other.val ≠ source.val := Ne.symm hvalne
  by_cases hsourceDelete : target.val + 1 = source.val
  · by_cases hotherDelete : target.val + 1 = other.val
    · exfalso
      apply hne
      apply Fin.ext
      omega
    · by_cases hotherAdd : other.val + 1 = target.val
      · simpa [hammingAdjacentChannel, hsourceDelete,
          hotherDelete, hotherAdd, hvalne, hvalne'] using
          (deleteChannel_orthogonal_addChannel
            (k + source.val) (k + other.val) f g)
      · simp [hammingAdjacentChannel, hsourceDelete,
          hotherAdd, hvalne,           coordinateDot, dot]
  · by_cases hsourceAdd : source.val + 1 = target.val
    · by_cases hotherDelete : target.val + 1 = other.val
      · calc
          coordinateDot
              (hammingAdjacentChannel n k L target source f)
              (hammingAdjacentChannel n k L target other g) =
            coordinateDot
              (hammingAdjacentChannel n k L target other g)
              (hammingAdjacentChannel n k L target source f) :=
                coordinateDot_comm _ _
          _ = 0 := by
            simpa [hammingAdjacentChannel, hsourceDelete,
              hsourceAdd, hotherDelete, hvalne, hvalne'] using
              (deleteChannel_orthogonal_addChannel
                (k + other.val) (k + source.val) g f)
      · by_cases hotherAdd : other.val + 1 = target.val
        · exfalso
          apply hne
          apply Fin.ext
          omega
        · simp [hammingAdjacentChannel, hsourceDelete,
            hsourceAdd, hotherDelete, hotherAdd,
            coordinateDot, dot]
    · simp [hammingAdjacentChannel, hsourceDelete,
        hsourceAdd, coordinateDot, dot]
end MetricCodes.Boolean
