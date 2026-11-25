-- Prove2me | solution 1 for GlobalTheory.SgLoc.PtAlg.isUnit_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:18:19.499323+00:00
-- url     : https://prove2.me/submissions/8f9afbc6-ee64-4e70-88dc-7d5fd5e09d15

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RowRawRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SameBlockAppend
import Theorems.Thm_GlobalTheory_SgLoc_PtAlg_det_snoc
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks


section
open ValuativeRel MeasureTheory ComplexConjugate Formalism.MainNotions.S.Loc GlobalTheory.SgLoc
open scoped ComplexOrder
namespace GlobalTheory.SgLoc.PtAlg
variable {E : Type} [CommRing E]
private theorem isUnit_det_of_mem_UH_Hpk (bs : List (Eˣ × ℕ+)) :
    ∀ (n : ℕ) (hn : (bs.map (fun b => (b.2 : ℕ))).sum = n),
      IsUnit (Pt.mat (⟨bs, hn⟩ : Pt E n)).det := by
  induction bs using List.reverseRecOn with
  | nil =>
    intro n hn
    have hn' : n = 0 := by rw [← hn]; simp
    subst hn'
    simp
  | append_singleton bs x ih =>
    obtain ⟨t, s⟩ := x
    intro n hn
    have hn' : n = (bs.map (fun b => (b.2 : ℕ))).sum + s := by rw [← hn]; simp
    subst hn'
    have hu := ih _ rfl
    change IsUnit (Pt.snoc (⟨bs, rfl⟩ : Pt E _) t s).mat.det
    rcases det_snoc (⟨bs, rfl⟩ : Pt E _) t s with h1 | h1
    · rw [h1]
      exact hu.mul ((Units.isUnit t).pow _)
    · rw [h1]
      exact (hu.mul ((Units.isUnit t).pow _)).neg
end GlobalTheory.SgLoc.PtAlg
namespace GlobalTheory.SgLoc
end GlobalTheory.SgLoc
end

set_option autoImplicit false
open ValuativeRel MeasureTheory ComplexConjugate Formalism.MainNotions.S.Loc GlobalTheory.SgLoc
open scoped ComplexOrder
open GlobalTheory GlobalTheory.SgLoc GlobalTheory.SgLoc.PtAlg
variable {E : Type} [CommRing E]
namespace GlobalTheory.SgLoc.PtAlg
theorem _root_.solution {m : ℕ} (h : Pt E m) : IsUnit h.mat.det := by
  exact isUnit_det_of_mem_UH_Hpk h.blocks m h.size
end GlobalTheory.SgLoc.PtAlg
