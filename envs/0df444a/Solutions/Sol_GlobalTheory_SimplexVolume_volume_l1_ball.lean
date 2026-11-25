-- Prove2me | solution 1 for GlobalTheory.SimplexVolume.volume_l1_ball
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:02:35.692669+00:00
-- url     : https://prove2.me/submissions/8a63b452-3171-40aa-b495-40641a43635d

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_VolumePosSimplexLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory NumberField Finset
open GlobalTheory GlobalTheory.SimplexVolume
namespace GlobalTheory.SimplexVolume
theorem _root_.solution (ι : Type) [Fintype ι] [Nonempty ι] (L : ℝ) (hL : 0 ≤ L) :
    volume {x : ι → ℝ | ∑ i, |x i| ≤ L} =
      2 ^ Fintype.card ι * ENNReal.ofReal (L ^ Fintype.card ι / (Fintype.card ι).factorial) := by
  have h := MeasureTheory.volume_sum_rpow_le ι (p := 1) le_rfl L
  simp only [Real.rpow_one, div_one, one_add_one_eq_two, Real.Gamma_two, mul_one,
    Real.Gamma_nat_eq_factorial] at h
  rw [h, ← ENNReal.ofReal_pow hL, ← ENNReal.ofReal_mul (by positivity)]
  have h2 : (2 : ENNReal) ^ Fintype.card ι = ENNReal.ofReal (2 ^ Fintype.card ι) := by
    rw [ENNReal.ofReal_pow (by norm_num)]; simp
  rw [h2, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring
end GlobalTheory.SimplexVolume
