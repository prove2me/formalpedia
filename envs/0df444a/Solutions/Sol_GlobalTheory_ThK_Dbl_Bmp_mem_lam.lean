-- Prove2me | solution 1 for GlobalTheory.ThK.Dbl.Bmp.mem_lam
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:24:46.007828+00:00
-- url     : https://prove2.me/submissions/57074f99-de63-4d12-8788-686004f3061d

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_MemLam

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.Bmp
open Matrix
variable {O K : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field K] [Algebra O K] [IsFractionRing O K]
variable {a : O} {n d : ℕ}
omit [IsDomain O] [IsPrincipalIdealRing O] [IsFractionRing O K]
namespace GlobalTheory.ThK.Dbl.Bmp
theorem _root_.solution {Y : Matrix (Fin n) (Fin d) K} : Y ∈ lam K a n d ↔ ∃ α : Matrix (Fin n) (Fin d) O, a • α.map (algebraMap O K) = Y := by
  simp only [lam, LinearMap.mem_range, LinearMap.smul_apply, LinearMap.mapMatrix_apply, Algebra.coe_linearMap]
end GlobalTheory.ThK.Dbl.Bmp
