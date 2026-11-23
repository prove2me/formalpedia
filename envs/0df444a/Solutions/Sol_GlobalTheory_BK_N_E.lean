-- Prove2me | solution 1 for GlobalTheory.BK.N_E
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:59:55.200494+00:00
-- url     : https://prove2.me/submissions/6249e7da-cdef-474f-83be-f25cad5bd363

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_NormPowLeNormFactorial
import Theorems.Thm_GlobalTheory_BK_coeff_N

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology
variable (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K]
variable {O K}
omit [IsUltrametricDist K] [IsUnitBall O K]
namespace GlobalTheory.BK
theorem _root_.solution (l e : ℕ) : N K (E K l e) = (e : K⟦X⟧) * X ^ e := by
  ext n
  rw [coeff_N, E, ← map_natCast (C : K →+* K⟦X⟧) l, ← map_natCast (C : K →+* K⟦X⟧) e,
    coeff_C_mul, map_add, coeff_X_pow, coeff_C]
  by_cases h0 : n = 0
  · subst h0
    split_ifs with h1
    · subst h1; simp
    all_goals simp_all
  · split_ifs <;> simp_all
end GlobalTheory.BK
