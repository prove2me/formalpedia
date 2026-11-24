-- Prove2me | solution 1 for GlobalTheory.SW.HaarAlg.exists_natCast_smul_intM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:26:09.342656+00:00
-- url     : https://prove2.me/submissions/c2b92918-48cc-4788-8672-8802491d68fc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FinsumQuotientOfLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RationalSchwartzBruhatAlgebraIntegralLinear

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HaarAlg
variable {K : Type} [Field K] {κ ι : Type}
namespace GlobalTheory.SW.HaarAlg
theorem _root_.solution [NumberField K] [Fintype κ] [Fintype ι] (b : Matrix κ ι K) :
    ∃ N : ℕ, 0 < N ∧ IntM ((N : K) • b) := by
  classical
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ
    (Finset.univ.image fun p : κ × ι => b p.1 p.2)
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy0, fun k i => ?_⟩
  have h := hy (b k i) (Finset.mem_image.mpr ⟨(k, i), Finset.mem_univ _, rfl⟩)
  rw [Matrix.smul_apply, smul_eq_mul]
  rw [zsmul_eq_mul] at h
  rcases Int.natAbs_eq y with e | e
  · rw [e, Int.cast_natCast] at h; exact h
  · rw [e, Int.cast_neg, Int.cast_natCast, neg_mul] at h
    simpa using h.neg
end GlobalTheory.SW.HaarAlg
