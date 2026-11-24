-- Prove2me | solution 1 for GlobalTheory.Cyc.Model.isCyc_chi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:06:53.205054+00:00
-- url     : https://prove2.me/submissions/ca1d3ac8-73f5-466b-8371-73877c045d88

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_PowLtFirstRadius

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Cyc GlobalTheory.Cyc.Model
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc Polynomial
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.Cyc.Model
theorem _root_.solution : IsCyc (chi (l := l)) := by
  intro g m ζ hζ
  refine ⟨(PadicInt.toZModPow m (chiZ g : ℤ_[l])).val, ?_, ?_⟩
  · have : ‖(chiZ g : ℤ_[l]) - ((PadicInt.toZModPow m (chiZ g : ℤ_[l])).val : ℤ_[l])‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
      rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub,
        map_natCast, ZMod.natCast_zmod_val, sub_self]
    rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_natCast] at this
    exact this
  · exact cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (GQ l) (Om l) g) ζ hζ
end GlobalTheory.Cyc.Model
