-- Prove2me | solution 1 for N25.GlobalKummer.rational_preimage_of_divisionClass_zero
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:30:42.621299+00:00
-- url     : https://prove2.me/submissions/7361d1b4-1099-454b-a422-35307badbc28

import Theorems.Thm_N25_GlobalKummer_class_eq_iff
import Definitions.Def_N25_GlobalKummer

set_option autoImplicit false

namespace N25.GlobalKummer

/-- The final pointwise use of G0: a zero division class gives a rational
preimage under the selected endomorphism. -/
theorem _root_.solution
    (hPhi : PhiFiveZero) (P : ↥M) (Q : J) (hQ : piEnd Q = (P : J))
    (hc : groupCohomology.H1π (vRep hPhi) (divisionCocycle hPhi P Q hQ) = 0) :
    ∃ R : ↥M, piM R = P := by
  have hzero : piEnd (0 : J) = ((0 : ↥M) : J) := map_zero _
  have hc0 : divisionCocycle hPhi (0 : ↥M) (0 : J) hzero = 0 := by
    ext σ
    apply Subtype.ext
    change σ • (0 : J) - 0 = 0
    rw [smul_zero (A := J) σ, sub_self]
  have hclass :
      groupCohomology.H1π (vRep hPhi) (divisionCocycle hPhi P Q hQ) =
        groupCohomology.H1π (vRep hPhi) (divisionCocycle hPhi 0 0 hzero) := by
    rw [hc0, map_zero, hc]
  have hmem := (class_eq_iff hPhi P 0 Q 0 hQ hzero).mp hclass
  simpa only [sub_zero, AddMonoidHom.mem_range] using hmem

end N25.GlobalKummer
