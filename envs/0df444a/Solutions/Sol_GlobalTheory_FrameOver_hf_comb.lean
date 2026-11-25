-- Prove2me | solution 1 for GlobalTheory.FrameOver.hf_comb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:30:31.575643+00:00
-- url     : https://prove2.me/submissions/4abc2ac2-3a02-4e49-96c8-b61cb55f16a4

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardSubmoduleAndHomLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatticeCountBoundFrames
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_FrameBasic_hf_conj
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
open GlobalTheory GlobalTheory.FrameOver
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.FrameOver
theorem _root_.solution (L : LocE F E) {n : ℕ} {H : Matrix (Fin n) (Fin n) E} (h : IsHerm L H)
    {ι : Type} [Fintype ι] (B B' : Matrix ι ι E) (v w : ι → Fin n → E) :
    (Matrix.of fun i j => hf L H (∑ k, B k i • v k) (∑ k, B' k j • w k)) =
      B.transpose * (Matrix.of fun i j => hf L H (v i) (w j)) * B'.map L.cj := by
  have key : ∀ (α : ι → E) (g : ι → Fin n → E) (y : Fin n → E),
      hf L H (∑ i, α i • g i) y = ∑ i, α i * hf L H (g i) y := fun α g y => by
    change GlobalTheory.FrameBasic.hfL L H y _ = _
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul]; rfl
  ext i j
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  rw [GlobalTheory.FrameBasic.hf_conj L h, key, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_mul, ← GlobalTheory.FrameBasic.hf_conj L h, key, Finset.mul_sum]
  exact Finset.sum_congr rfl fun m _ => by ring
end GlobalTheory.FrameOver
