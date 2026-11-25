-- Prove2me | solution 1 for GlobalTheory.HL.Inhab.isSD_stdLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:00:02.344425+00:00
-- url     : https://prove2.me/submissions/6697e062-4b07-464f-bffa-1f08c2bfbb7b

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIntegralIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFourInverseMul
import Theorems.Thm_GlobalTheory_HL_Inhab_cj_int
import Theorems.Thm_GlobalTheory_HL_Inhab_mem_stdLat
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
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.Inhab
open GlobalTheory.HL.Model
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.Inhab
theorem _root_.solution (L : LocE F E) {n : ℕ} (H K : Matrix (Fin n) (Fin n) E) (hH : IsIntM L H)
    (hK : IsIntM L K) (hKH : K * H = 1) : IsSD L H (stdLat L n) := by
  refine ⟨⟨Submodule.fg_span (Set.finite_range _), ?_⟩, ?_⟩
  · rw [eq_top_iff]
    intro v _
    have hsum : v = ∑ i, v i • (Pi.single i 1 : Fin n → E) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hsum]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Submodule.subset_span ⟨i, rfl⟩))
  · intro y
    rw [mem_stdLat]
    constructor
    · intro h j
      have hrow : ∀ i, (Matrix.mulVec H fun k => L.cj (y k)) i ∈ L.O := by
        intro i
        have hs : (Pi.single i 1 : Fin n → E) ∈ stdLat L n := (mem_stdLat L _).2 fun k => by
          rw [Pi.single_apply]
          split_ifs
          · exact one_mem _
          · exact zero_mem _
        have := h _ hs
        simpa [hf, Pi.single_apply, Matrix.mulVec, dotProduct] using this
      have hcK : (fun k => L.cj (y k)) = Matrix.mulVec K (Matrix.mulVec H fun k => L.cj (y k)) := by
        rw [Matrix.mulVec_mulVec, hKH, Matrix.one_mulVec]
      have hcj : (Matrix.mulVec K (Matrix.mulVec H fun k => L.cj (y k))) j ∈ L.O := by
        simp only [Matrix.mulVec, dotProduct]
        exact Subring.sum_mem _ fun i _ => mul_mem (hK j i) (hrow i)
      rw [← hcK] at hcj
      have := cj_int L hcj
      simpa [L.cj_cj] using this
    · intro h x hx
      rw [mem_stdLat] at hx
      exact Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ =>
        mul_mem (mul_mem (hx i) (hH i j)) (cj_int L (h j))
end GlobalTheory.HL.Inhab
