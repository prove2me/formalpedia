-- Prove2me | solution 1 for GlobalTheory.SgLoc.Top.mem_R_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:02:29.190804+00:00
-- url     : https://prove2.me/submissions/4a329c67-c4d7-4769-8c11-2e6bb3cae1a9

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RowRawRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_T2SpaceOfIsNonarchimedeanLocalFieldFlagMeasures
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
open ValuativeRel MeasureTheory Formalism.MainNotions.S.Loc
open GlobalTheory GlobalTheory.SgLoc GlobalTheory.SgLoc.Top
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable [MeasurableSpace E]
namespace GlobalTheory.SgLoc.Top
theorem _root_.solution (M : Model F E) (g : SplitG M.L) (hg : M.split = some g) (x : E) :
    x ∈ M.R ↔ ∃ a b : 𝒪[F], g.q ∣ a - b ∧ g.e x = ((a : F), (b : F)) := by
  simp only [Model.R, hg]
  rw [Subring.mem_comap, Subring.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    refine ⟨y.1, y.2, ?_, ?_⟩
    · rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq]
      exact hy
    · exact hyx.symm
  · rintro ⟨a, b, hab, hx⟩
    refine ⟨(a, b), ?_, ?_⟩
    · show Ideal.Quotient.mk _ a = Ideal.Quotient.mk _ b
      rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
      exact hab
    · exact hx.symm
end GlobalTheory.SgLoc.Top
