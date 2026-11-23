-- Prove2me | solution 1 for GlobalTheory.BK.A_le_S
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:05:09.855664+00:00
-- url     : https://prove2.me/submissions/78795b37-7508-415d-bd4c-cf74b80e6f2d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_NormPowLeNormFactorial
import Theorems.Thm_GlobalTheory_BK_tendsto_wS

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
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K]
include l
namespace GlobalTheory.BK
theorem _root_.solution (e : ℕ) [NeZero e] : A O K ≤ S O K e := fun _ hf =>
  ⟨fun n => mul_le_one₀ (hf n) (wS_nonneg _ _) (wS_le_one _ _),
    squeeze_zero (fun n => mul_nonneg (norm_nonneg _) (wS_nonneg e n))
      (fun n => mul_le_of_le_one_left (wS_nonneg e n) (hf n)) (tendsto_wS l e)⟩
end GlobalTheory.BK
