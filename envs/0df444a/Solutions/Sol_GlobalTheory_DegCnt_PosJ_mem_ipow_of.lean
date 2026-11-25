-- Prove2me | solution 1 for GlobalTheory.DegCnt.PosJ.mem_ipow_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:57:06.406903+00:00
-- url     : https://prove2.me/submissions/49322ffb-bd4b-4dfa-8d5e-96525b5cc778

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeadingMinorsProdDenominatorUnitriangularFactors
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesPairingStabilizerBlockDiagonal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormalFormFlagLatticesNearUnderStabiliser
import Theorems.Thm_GlobalTheory_DegCnt_PosJ_ipow_add
import Theorems.Thm_GlobalTheory_DegCnt_PosJ_ipow_mul
import Theorems.Thm_GlobalTheory_DegCnt_PosJ_one_mem_ipow
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.PosJ
variable {K : Type} [Field K] [NumberField K]
namespace GlobalTheory.DegCnt.PosJ
theorem _root_.solution {𝔡 : Ideal (𝓞 K)} (h : 𝔡 ≠ ⊥) {m n : ℤ} {x : K}
    (hx : ∀ y ∈ ipow 𝔡 m, y * x ∈ ipow 𝔡 (m + n)) : x ∈ ipow 𝔡 n := by
  have h1 : (1 : K) ∈ ipow 𝔡 (-m) * ipow 𝔡 m := by
    rw [← ipow_add h, neg_add_cancel]; exact one_mem_ipow 𝔡
  have : ∀ u ∈ ipow 𝔡 (-m) * ipow 𝔡 m, u * x ∈ ipow 𝔡 n := by
    intro u hu
    refine Submodule.mul_induction_on hu (fun a ha b hb => ?_) (fun a b ha hb => ?_)
    · have := ipow_mul h ha (hx b hb)
      rwa [neg_add_cancel_left, ← mul_assoc] at this
    · rw [add_mul]; exact add_mem ha hb
  simpa using this 1 h1
end GlobalTheory.DegCnt.PosJ
