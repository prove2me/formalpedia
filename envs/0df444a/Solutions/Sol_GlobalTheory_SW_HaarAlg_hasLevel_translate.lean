-- Prove2me | solution 1 for GlobalTheory.SW.HaarAlg.hasLevel_translate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:41:08.189441+00:00
-- url     : https://prove2.me/submissions/a4c04420-b837-4964-89af-3880e18a79fa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FinsumQuotientOfLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RationalSchwartzBruhatAlgebraIntegralLinear
import Theorems.Thm_GlobalTheory_SW_HaarAlg_intM_add
import Theorems.Thm_GlobalTheory_SW_HaarAlg_intM_natCast_smul
import Theorems.Thm_GlobalTheory_SW_HaarAlg_hasLevel_mul

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
theorem _root_.solution {R N : ℕ} {φ : Matrix κ ι K → ℂ} (h : HasLevel R φ) {b : Matrix κ ι K}
    (hb : IntM ((N : K) • b)) : HasLevel (R * N) fun x => φ (x - b) := by
  refine ⟨fun x hx => ?_, fun x y hy => ?_⟩
  · have e : ((R * N : ℕ) : K) • x = (N : K) • ((R : K) • (x - b)) + (R : K) • ((N : K) • b) := by
      rw [Nat.cast_mul]; module
    rw [e]
    exact intM_add (intM_natCast_smul N (h.1 _ hx)) (intM_natCast_smul R hb)
  · show φ _ = φ _
    rw [add_sub_right_comm]
    exact (hasLevel_mul h N).2 _ y hy
end GlobalTheory.SW.HaarAlg
