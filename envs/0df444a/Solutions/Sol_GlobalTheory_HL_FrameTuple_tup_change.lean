-- Prove2me | solution 1 for GlobalTheory.HL.FrameTuple.tup_change
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:39:05.71937+00:00
-- url     : https://prove2.me/submissions/a9789d9e-7a3b-4b63-b4c8-1f223bc97273

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsNondegenerateTupleComplementFixer
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
noncomputable section
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FrameTuple
variable {E V : Type} [CommRing E] [AddCommGroup V] [Module E V] {m : ℕ}
namespace GlobalTheory.HL.FrameTuple
theorem _root_.solution (t : E) (g g' p p' : Fin m → V) (u u' : Matrix (Fin m) (Fin m) E)
    (hp : ∀ j, p j = ∑ i, u i j • g i) (hp' : ∀ j, p' j = ∑ i, u' i j • g' i) (j) :
    tup t p p' j = ∑ i, (Matrix.fromBlocks u (t • (u' - u)) 0 u') i j • tup t g g' i := by
  rcases j with j | j
  · simp [tup, Fintype.sum_sum_type, hp]
  · simp only [tup, Fintype.sum_sum_type, hp, hp', Sum.elim_inl, Sum.elim_inr,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib, Finset.smul_sum, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    module
end GlobalTheory.HL.FrameTuple
