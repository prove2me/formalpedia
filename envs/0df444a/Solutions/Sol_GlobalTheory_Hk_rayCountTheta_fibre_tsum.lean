-- Prove2me | solution 1 for GlobalTheory.Hk.rayCountTheta_fibre_tsum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:35:05.536575+00:00
-- url     : https://prove2.me/submissions/04238ff8-3acb-4012-ab6b-0e1fbda68518

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_QFormCountStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ThetaQFormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassIdealCountEqNcardShiftedBinaryFormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayCountThetaFibreCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
open GlobalTheory GlobalTheory.Hk
namespace GlobalTheory.Hk
theorem _root_.solution {ι : Type} (Q : ι → ℝ) (q : ι → ℕ) (hq : ∀ v, Q v = q v) (t : ℝ)
    (hs : Summable fun v => Real.exp (-(t * Q v))) :
    ∑' n : ℕ, (({v | Q v = (n : ℕ)}.ncard : ℕ) : ℝ) * Real.exp (-(t * n)) = ∑' v, Real.exp (-(t * Q v)) := by
  have hf := hs.hasSum.tsum_fiberwise q
  rw [← hf.tsum_eq]
  congr 1
  funext n
  have hset : {v | Q v = (n : ℕ)} = q ⁻¹' {n} := by
    ext v
    simp [hq]
  calc (({v | Q v = (n : ℕ)}.ncard : ℕ) : ℝ) * Real.exp (-(t * n))
      = ∑' _ : q ⁻¹' {n}, Real.exp (-(t * n)) := by
        rw [tsum_const, hset, Nat.card_coe_set_eq, nsmul_eq_mul]
    _ = ∑' b : q ⁻¹' {n}, Real.exp (-(t * Q b)) := by
        congr 1
        funext b
        rw [hq b, show q b = n from b.2]
end GlobalTheory.Hk
