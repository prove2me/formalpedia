-- Prove2me | solution 1 for GlobalTheory.FrameGram.gram_change
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:39:26.504797+00:00
-- url     : https://prove2.me/submissions/94d23342-d637-4334-8d4e-9c4da00c677c

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DetGramTwoFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FrameUnipotentUnitriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FrameLatticeGramDetAndMinorsOrbitInvariant
import Theorems.Thm_GlobalTheory_FrameGram_hf_sum_left
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_FrameBasic_hf_conj
import Theorems.Thm_GlobalTheory_HL_FrameTri_hf_sum_left
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.FrameGram
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.FrameGram
theorem _root_.solution (L : LocE F E) {n : ℕ} {H : Matrix (Fin n) (Fin n) E} (h : IsHerm L H)
    {ι : Type} [Fintype ι] (u u' v v' : ι → Fin n → E) (P P' : Matrix ι ι E)
    (hv : ∀ j, v j = ∑ i, P i j • u i) (hv' : ∀ j, v' j = ∑ i, P' i j • u' i) :
    (Matrix.of fun a b => hf L H (v' b) (v a)) =
      (P.map L.cj).transpose * (Matrix.of fun a b => hf L H (u' b) (u a)) * P' := by
  ext a b
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  rw [hv', hf_sum_left]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm, GlobalTheory.FrameBasic.hf_conj L h, hv, hf_sum_left, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, ← GlobalTheory.FrameBasic.hf_conj L h]
end GlobalTheory.FrameGram
