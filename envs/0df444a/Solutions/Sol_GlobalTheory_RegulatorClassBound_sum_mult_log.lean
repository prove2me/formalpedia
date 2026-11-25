-- Prove2me | solution 1 for GlobalTheory.RegulatorClassBound.sum_mult_log
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:34:32.844354+00:00
-- url     : https://prove2.me/submissions/4b58406f-91d8-4a95-bca1-0991129ec4cc

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CovolumeLeSumVolumeOfCover
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_VolumePosSimplexLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RegulatorLeSumSmallIdealsInClass

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory NumberField Finset
open GlobalTheory GlobalTheory.RegulatorClassBound
open NumberField.mixedEmbedding NumberField.InfinitePlace NumberField.Units
  NumberField.Units.dirichletUnitTheorem Module
open scoped nonZeroDivisors
namespace GlobalTheory.RegulatorClassBound
theorem _root_.solution (K : Type) [Field K] [NumberField K] (a : 𝓞 K) (ha : a ≠ 0) :
    ∑ w : InfinitePlace K, (w.mult : ℝ) * Real.log (w (a : K)) =
      Real.log (Ideal.absNorm (Ideal.span {a}) : ℝ) := by
  have ha' : (a : K) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.2 ha
  have h := prod_eq_abs_norm (a : K)
  have h2 : (Ideal.absNorm (Ideal.span {a}) : ℝ) = ((|Algebra.norm ℚ (a : K)| : ℚ) : ℝ) := by
    rw [Ideal.absNorm_span_singleton, ← Algebra.coe_norm_int, Nat.cast_natAbs]
    push_cast; rfl
  rw [h2, ← h, Real.log_prod (fun w _ => pow_ne_zero _ (pos_iff.2 ha').ne')]
  simp [Real.log_pow]
end GlobalTheory.RegulatorClassBound
