-- Prove2me | solution 1 for GlobalTheory.RowStab.star_mem_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:12:14.004833+00:00
-- url     : https://prove2.me/submissions/9e654621-f47b-41e7-9520-28c74c2aa69f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemIpowSmulOfSmulMem
import Theorems.Thm_GlobalTheory_RowStab_star_integral

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
theorem _root_.solution {x : K} (hx : x ∈ (1 : FractionalIdeal (𝓞 K)⁰ K)) :
    star x ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
  rw [FractionalIdeal.mem_one_iff] at *
  obtain ⟨y, rfl⟩ := hx
  obtain ⟨y', hy'⟩ := star_integral y
  exact ⟨y', hy'⟩
end GlobalTheory.RowStab
