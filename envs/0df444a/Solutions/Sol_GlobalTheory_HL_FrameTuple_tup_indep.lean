-- Prove2me | solution 1 for GlobalTheory.HL.FrameTuple.tup_indep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:34:08.169623+00:00
-- url     : https://prove2.me/submissions/b9cb6869-2b86-4c41-b283-fe126c4c4950

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
theorem _root_.solution {t θ : E} (h : θ * t = 1) {g g' : Fin m → V}
    (hli : LinearIndependent E (Sum.elim g g')) : LinearIndependent E (tup t g g') := by
  rw [Fintype.linearIndependent_iff] at hli ⊢
  intro c hc
  have key := hli (Sum.elim (fun a => c (Sum.inl a) - t * c (Sum.inr a)) fun b => t * c (Sum.inr b))
    (by
      rw [← hc]
      simp only [Fintype.sum_sum_type, tup, Sum.elim_inl, Sum.elim_inr, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [sub_smul, smul_sub, smul_smul, mul_comm t]
      abel)
  have h2 : ∀ b, c (Sum.inr b) = 0 := fun b => by
    have := key (Sum.inr b)
    simp only [Sum.elim_inr] at this
    linear_combination θ * this - c (Sum.inr b) * h
  rintro (a | b)
  · have := key (Sum.inl a)
    simpa [h2] using this
  · exact h2 b
end GlobalTheory.HL.FrameTuple
