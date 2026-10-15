-- Prove2me | solution 1 for OAI.SquareRootDegree.TableRounding.event_indicator
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:35:41.844665+00:00
-- url     : https://prove2.me/submissions/40e91d0c-47e7-4d1b-b715-2f7ece3047e4

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BooleanFunctions/Rounding.lean:L105-L133
-- (upload_full_project.md Phase 4): solution for node OAI.SquareRootDegree.TableRounding.event_indicator. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_SquareRootDegree
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Walsh
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Conditioning
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Blocks
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Projection
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_FiniteCLT
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Observations
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_SmoothGaussian
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_SmoothSelector
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_GaussianGain
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_MomentTransfer
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_SoftEvent
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Switching
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Rounding

-- ---- from OAI.Combinatorics.BooleanFunctions.Rounding ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e

namespace OAI

open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real

noncomputable section

attribute [local instance] Classical.propDecidable

namespace SquareRootDegree
namespace FiniteRounding

end FiniteRounding
end SquareRootDegree

namespace SquareRootDegree
namespace TableRounding
open FiniteRounding SoftEvent
attribute [local instance] Classical.propDecidable
variable {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β]

omit [Fintype β] in
theorem event_indicator (S : β → ι) (L : ι → β → Bool) (x : β × (ι → β)) :
    (if tableEvent S L x then (1:ℝ) else 0) =
      softWeight (fun i b => if S b = i then 1 else 0) (fun i b => bit (L i b)) x := by
  have hs : (∑ i, (if S x.1 = i then (1:ℝ) else 0) *
      ∏ j ∈ Finset.univ.erase i, bit (L j (x.2 j))) =
      ∏ j ∈ Finset.univ.erase (S x.1), bit (L j (x.2 j)) := by simp
  unfold softWeight
  rw [hs]
  have hp : (∏ j, bit (L j (x.2 j))) = bit (L (S x.1) (x.2 (S x.1))) *
      ∏ j ∈ Finset.univ.erase (S x.1), bit (L j (x.2 j)) :=
    (Finset.mul_prod_erase _ _ (Finset.mem_univ _)).symm
  rw [hp]
  by_cases h : ∀ i, i ≠ S x.1 → L i (x.2 i) = true
  · have he : (∏ j ∈ Finset.univ.erase (S x.1), bit (L j (x.2 j))) = 1 := by
      apply Finset.prod_eq_one
      intro j hj
      simp [bit,h j (Finset.mem_erase.mp hj).1]
    rw [he]
    cases hb : L (S x.1) (x.2 (S x.1))
    · simp only [tableEvent,hb,true_and,bit,Bool.false_eq_true,ite_false,zero_mul,sub_zero]
      rw [ite_eq_left h]
    · simp [tableEvent,hb,bit]
  · obtain ⟨j,hj,hb⟩ := by simpa only [not_forall,Classical.not_imp] using h
    have he : (∏ j ∈ Finset.univ.erase (S x.1), bit (L j (x.2 j))) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hj,Finset.mem_univ _⟩)
      cases ht : L j (x.2 j) <;> simp_all [bit]
    rw [he]
    simp [tableEvent,h]

end TableRounding
end SquareRootDegree

end

end OAI

-- ---- platform node ----
open OAI OAI.SquareRootDegree OAI.SquareRootDegree.TableRounding
open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real
attribute [local instance] Classical.propDecidable
open FiniteRounding SoftEvent
attribute [local instance] Classical.propDecidable
variable {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β]

omit [Fintype β] in
theorem solution (S : β → ι) (L : ι → β → Bool) (x : β × (ι → β)) :
    (if tableEvent S L x then (1:ℝ) else 0) =
      softWeight (fun i b => if S b = i then 1 else 0) (fun i b => bit (L i b)) x := by
  first
    | exact OAI.SquareRootDegree.TableRounding.event_indicator S L x
    | exact OAI.SquareRootDegree.TableRounding.event_indicator
    | (apply OAI.SquareRootDegree.TableRounding.event_indicator <;> assumption)
    | (intros; apply OAI.SquareRootDegree.TableRounding.event_indicator <;> assumption)
