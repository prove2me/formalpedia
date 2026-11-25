-- Prove2me | solution 1 for GlobalTheory.FunObj.unfTerm_coef_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:44:51.432002+00:00
-- url     : https://prove2.me/submissions/01d410df-b3f6-42d4-838c-cb9d07f274d7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Theorems.Thm_GlobalTheory_FunObj_invVol_pos
import Theorems.Thm_GlobalTheory_SplitFlip_CondLE_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal
noncomputable section
open GlobalTheory GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx
variable {k : Type*} [Field k] (G : Grid k)
variable {G}
variable (hs : 1 ≤ G.s)
variable {hs}
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k)
variable {J : G.Level} (keep : Bool) (ρ : Reps hs J) (T : G.Args → ℂ)
namespace GlobalTheory.FunObj
theorem _root_.solution (hJ : ∀ j, 0 < j → j < G.m → IsOpen (J (G.m, j) : Set (GL (Fin (G.rank (G.m, j))) k)) ∧
    J (G.m, j) ≤ KO k _) (β : Cosets hs J) : 0 < (unfTerm ψ ν keep ρ T β).coef := by
  refine Finset.prod_pos (R := ℚ) fun i _ => ?_
  obtain ⟨ho, hK⟩ := hJ (i + 1) (by omega) (by omega)
  have c1 : Continuous (toFrame hs (j := i + 1) (by omega)) :=
    Continuous.units_map _ (continuous_id.matrix_reindex _ _)
  have c2 : Continuous (toFrame hs (j := i + 1) (by omega)).symm :=
    Continuous.units_map _ (continuous_id.matrix_reindex _ _)
  refine invVol_pos ?_ ?_
  · rw [conjLevel, Subgroup.map_equiv_eq_comap_symm', Subgroup.map_equiv_eq_comap_symm']
    exact (ho.preimage ((continuous_const.mul continuous_id).mul continuous_const)).preimage c2
  · exact ((isCompact_KO.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ ho) hK).image
      ((continuous_const.mul continuous_id).mul continuous_const)).image c1
end GlobalTheory.FunObj
