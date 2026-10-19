-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.QuadraticTail.finite_product_error
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:31:35.992694+00:00
-- url     : https://prove2.me/submissions/4f3c5c97-0db9-4ee4-8198-d3727ea69379

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/QuadraticTail.lean:L543-L584
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.QuadraticTail.finite_product_error. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail

-- ---- from OAI.Analysis.Littlewood.QuadraticTail ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement).
private abbrev Finset.prod_le_one₀ := @Finset.prod_le_one

namespace OAI

universe uI uZ

namespace AsymptoticallyMinimalLittlewood
namespace QuadraticTail
noncomputable section
open MeasureTheory Filter Topology Complex
open scoped BigOperators ContDiff

/-- Tensoring finitely many uniformly bounded approximations preserves a
uniform O(1/T) error; both target functions may depend on T. -/
lemma finite_product_error {I : Type uI} {Z : Type uZ} (S : Finset I)
    (f h : I → ℝ → Z → ℂ)
    (hh : ∀ i ∈ S, ∀ T z, ‖h i T z‖≤1)
    (hf : ∀ i ∈ S, ∃ C : ℝ, 0≤C ∧ ∀ T, 1≤T → ∀ z, ‖f i T z-h i T z‖≤C/T) :
    ∃ C : ℝ, 0≤C ∧ ∀ T, 1≤T → ∀ z,
      ‖(∏ i ∈ S, f i T z)-(∏ i ∈ S, h i T z)‖ ≤ C/T := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0,le_rfl,by simp⟩
  | @insert i S hi ih =>
      obtain ⟨C,hC,hc⟩ := hf i (Finset.mem_insert_self _ _)
      obtain ⟨D,hD,hd⟩ := ih
        (fun j hj ↦ hh j (Finset.mem_insert_of_mem hj))
        (fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))
      refine ⟨(1+C)*D+C,by positivity,?_⟩
      intro T hT z
      have hT0 : 0<T := by linarith
      have hn : ‖f i T z‖ ≤ 1+C := by
        have hb := norm_sub_norm_le (f i T z) (h i T z)
        have hc' := hc T hT z
        have hh' := hh i (Finset.mem_insert_self _ _) T z
        have hcT : C/T≤C := (div_le_self hC hT)
        linarith
      have hp : ‖∏ j ∈ S, h j T z‖≤1 := by
        rw [norm_prod]
        exact Finset.prod_le_one₀ (fun j _ ↦ norm_nonneg (h j T z)) (fun j hj ↦ hh j (Finset.mem_insert_of_mem hj) T z)
      rw [Finset.prod_insert hi, Finset.prod_insert hi]
      calc
        _ = ‖f i T z*((∏ j ∈ S, f j T z)-(∏ j ∈ S, h j T z)) +
          (f i T z-h i T z)*(∏ j ∈ S, h j T z)‖ := by congr 1; ring
        _ ≤ ‖f i T z‖*‖(∏ j ∈ S, f j T z)-(∏ j ∈ S, h j T z)‖ +
          ‖f i T z-h i T z‖*‖∏ j ∈ S, h j T z‖ := by
            simpa only [norm_mul] using norm_add_le
              (f i T z*((∏ j ∈ S, f j T z)-(∏ j ∈ S, h j T z)))
              ((f i T z-h i T z)*(∏ j ∈ S, h j T z))
        _ ≤ (1+C)*(D/T)+(C/T)*1 := by
          apply add_le_add
          · exact mul_le_mul hn (hd T hT z) (norm_nonneg _) (by positivity)
          · exact mul_le_mul (hc T hT z) hp (norm_nonneg _) (by positivity)
        _ = _ := by ring

end
end QuadraticTail
end AsymptoticallyMinimalLittlewood

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.QuadraticTail
open MeasureTheory Filter Topology Complex
open scoped BigOperators ContDiff


theorem solution.{uI,uZ} : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.QuadraticTail.finite_product_error.{uI,uZ} := @_root_.OAI.AsymptoticallyMinimalLittlewood.QuadraticTail.finite_product_error.{uI,uZ}
