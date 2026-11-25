-- Prove2me | solution 1 for GlobalTheory.RowStab.star_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:34:32.50329+00:00
-- url     : https://prove2.me/submissions/9249624c-377a-42cd-9020-afce19594e01

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemIpowSmulOfSmulMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.DegCnt
open scoped Pointwise nonZeroDivisors
open GlobalTheory GlobalTheory.RowStab
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace GlobalTheory.RowStab
theorem _root_.solution (y : 𝓞 K) : ∃ y' : 𝓞 K, (y' : K) = star (y : K) := by
  have h : IsIntegral ℤ (star (y : K)) := by
    exact (RingOfIntegers.isIntegral_coe y).map ((starRingEnd K).toIntAlgHom)
  exact ⟨⟨star (y : K), h⟩, rfl⟩
end GlobalTheory.RowStab
