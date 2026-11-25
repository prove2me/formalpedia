-- Prove2me | solution 1 for GroundTheory.Global.SemiLocal.valued_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:08:02.258201+00:00
-- url     : https://prove2.me/submissions/b2f0b9e9-46fa-4729-ba87-241244a0957f

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_ContinuousCompletionMap
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_LocalDegree
import Theorems.Thm_GroundTheory_Global_SemiLocal_valued_algebraMap_int_le_one
import Theorems.Thm_GroundTheory_Global_SemiLocal_valued_algebraMap_completion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open IsDedekindDomain NumberField WithZero
noncomputable section
open GroundTheory.Global.SemiLocal
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]
variable {ι : Type*} [Fintype ι]
namespace GroundTheory.Global.SemiLocal
theorem _root_.solution (ω : ι → 𝓞 L) (c : ι → v.adicCompletion K) (M : ℤᵐ⁰)
    (hM : ∀ j, Valued.v (c j) ≤ M) :
    Valued.v (∑ j, algebraMap (v.adicCompletion K) (w.adicCompletion L) (c j) *
      algebraMap (𝓞 L) (w.adicCompletion L) (ω j)) ≤ M ^ w.asIdeal.ramificationIdx (𝓞 K) := by
  apply Valuation.map_sum_le
  intro j _
  rw [map_mul, valued_algebraMap_completion]
  calc _ ≤ Valued.v (c j) ^ w.asIdeal.ramificationIdx (𝓞 K) * 1 :=
        mul_le_mul' le_rfl (valued_algebraMap_int_le_one w (ω j))
    _ ≤ _ := by rw [mul_one]; exact pow_le_pow_left' (hM j) _
end GroundTheory.Global.SemiLocal
