-- Prove2me | solution 1 for GlobalTheory.SgLoc.Top.R_le_O
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:46:59.436405+00:00
-- url     : https://prove2.me/submissions/498c1b96-193f-40e4-a2f6-716c264897c1

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RowRawRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_T2SpaceOfIsNonarchimedeanLocalFieldFlagMeasures
import Theorems.Thm_GlobalTheory_SgLoc_Top_mem_R_split
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
theorem _root_.solution (M : Model F E) : M.R ≤ M.L.O := by
  intro x hx
  cases hs : M.split with
  | none =>
    simp only [Model.R, hs] at hx
    exact hx
  | some g =>
    obtain ⟨a, b, -, hx'⟩ := (mem_R_split M g hs x).mp hx
    rw [M.L.O_def]
    have hab : IsIntegral 𝒪[F] ((a : F), (b : F)) := by
      refine ⟨(Polynomial.X - Polynomial.C a) * (Polynomial.X - Polynomial.C b),
        (Polynomial.monic_X_sub_C a).mul (Polynomial.monic_X_sub_C b), ?_⟩
      simp only [Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C,
        IsScalarTower.algebraMap_apply 𝒪[F] F (F × F), Prod.algebraMap_apply, Algebra.algebraMap_self,
        RingHom.id_apply]
      ext
      · simp
        left
        exact sub_self _
      · simp
        right
        exact sub_self _
    have hxe : x = g.e.symm ((a : F), (b : F)) := by rw [← hx', AlgEquiv.symm_apply_apply]
    rw [hxe]
    exact hab.map (g.e.symm.toAlgHom.restrictScalars 𝒪[F])
end GlobalTheory.SgLoc.Top
