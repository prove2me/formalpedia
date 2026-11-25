-- Prove2me | solution 1 for GlobalTheory.spanCovol_map_linearIsometry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:59:25.424783+00:00
-- url     : https://prove2.me/submissions/6e89890a-ee75-4e2f-a5ac-f012d4ae6127

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsOrthonormalOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LinearIndependentRealOfIntOfDiscrete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DiscreteTopologySpanOfLinearIndependent
import Theorems.Thm_GlobalTheory_spanCovol_eq_sqrt_det_gram
import Theorems.Thm_GlobalTheory_spanCovol_bot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.spanCovol_bot

set_option autoImplicit false
open scoped InnerProductSpace
open Module Submodule Matrix
open GlobalTheory
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory
theorem _root_.solution {L : Submodule ℤ E} (hL : L.FG) (T : E →ₗᵢ[ℝ] F) :
    spanCovol (L.map (T.toLinearMap.restrictScalars ℤ)) = spanCovol L := by
  have : Module.Finite ℤ L := .of_fg hL
  have : Module.Free ℤ L := free_of_fg hL
  let b := finBasis ℤ L
  rw [spanCovol_eq_sqrt_det_gram
    (b.map (L.equivMapOfInjective (T.toLinearMap.restrictScalars ℤ) T.injective)),
    spanCovol_eq_sqrt_det_gram b]
  congr 2
  ext i j
  exact T.inner_map_map _ _
end GlobalTheory
