-- Prove2me | solution 1 for GlobalTheory.RowStab.gen_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:40:35.257831+00:00
-- url     : https://prove2.me/submissions/1292c7f8-2319-480a-9134-6a29989b923c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemIpowSmulOfSmulMem
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
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.DegCnt
open scoped Pointwise nonZeroDivisors
open GlobalTheory GlobalTheory.RowStab
variable {K V ι : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
namespace GlobalTheory.RowStab
theorem _root_.solution (H : HermSpace K V) (J : Finset ι) (e ρ : ι → V) (c : ι → ι → K) (v : V) :
    gen H J e ρ c v = v + ∑ b ∈ J, (H.B v (e b) • ρ b - H.B v (ρ b) • e b +
      ∑ a ∈ J, (c a b * H.B v (e b)) • e a) := by
  simp [gen, LinearMap.sum_apply, mul_smul]
end GlobalTheory.RowStab
