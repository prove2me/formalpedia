-- Prove2me | solution 1 for GlobalTheory.RootEx.Model.coord_embedding
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:29.836905+00:00
-- url     : https://prove2.me/submissions/2ee8062c-4788-421a-8f79-e463bc787967

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol

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
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.Model
open GlobalTheory.SplitWeil GlobalTheory.RootEx
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}
variable [MeasurableSpace k]
namespace GlobalTheory.RootEx.Model
theorem _root_.solution (p : ℕ) : MeasurableEmbedding
    (fun (g : N k n c p) (rs : {rs : (n ⊕ Fin c) × (n ⊕ Fin c) // lev p rs.1 < lev p rs.2}) =>
      (g : GL (n ⊕ Fin c) k).val rs.1.1 rs.1.2) ∧ Function.Surjective
    (fun (g : N k n c p) (rs : {rs : (n ⊕ Fin c) × (n ⊕ Fin c) // lev p rs.1 < lev p rs.2}) =>
      (g : GL (n ⊕ Fin c) k).val rs.1.1 rs.1.2) := by
  have hs : Function.Surjective
      (fun (g : N k n c p) (rs : {rs : (n ⊕ Fin c) × (n ⊕ Fin c) // lev p rs.1 < lev p rs.2}) =>
      (g : GL (n ⊕ Fin c) k).val rs.1.1 rs.1.2) := by
    intro e
    refine ⟨mkNel p e, ?_⟩
    funext rs
    show mkN p e _ _ = _
    simp [mkN, rs.2]
  refine ⟨MeasurableEmbedding.of_measurable_inverse (g := mkNel (k := k) p) ?_ ?_ ?_ ?_, hs⟩
  · refine measurable_pi_lambda _ fun rs => ?_
    have h1 : Measurable (fun g : GL (n ⊕ Fin c) k => g.val) := comap_measurable _
    have h2 : Measurable (fun m : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k => m rs.1.1 rs.1.2) :=
      (measurable_pi_apply rs.1.2).comp (measurable_pi_apply rs.1.1)
    exact h2.comp (h1.comp measurable_subtype_coe)
  · rw [hs.range_eq]; exact MeasurableSet.univ
  · refine Measurable.subtype_mk ?_
    refine measurable_comap_iff.2 ?_
    refine measurable_pi_lambda _ fun r => measurable_pi_lambda _ fun s => ?_
    show Measurable fun e : {rs : (n ⊕ Fin c) × (n ⊕ Fin c) // lev p rs.1 < lev p rs.2} → k => mkN (k := k) p e r s
    by_cases h : lev p r < lev p s
    · simp only [mkN, Matrix.of_apply, dif_pos h]; exact measurable_pi_apply _
    · simp only [mkN, Matrix.of_apply, dif_neg h]; exact measurable_const
  · intro g
    ext r s
    show mkN (k := k) p (fun rs => (g : GL (n ⊕ Fin c) k).val rs.1.1 rs.1.2) r s = _
    by_cases h : lev p r < lev p s
    · simp [mkN, h]
    · simp only [mkN, Matrix.of_apply, dif_neg h]
      exact (mem_N_iff.1 g.2 r s (not_lt.1 h)).symm
end GlobalTheory.RootEx.Model
