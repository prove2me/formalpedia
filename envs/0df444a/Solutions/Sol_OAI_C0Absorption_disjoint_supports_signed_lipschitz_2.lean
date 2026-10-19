-- Prove2me | solution 2 for OAI.C0Absorption.disjoint_supports_signed_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:48:10.319769+00:00
-- url     : https://prove2.me/submissions/0981db13-394b-4069-b0cd-d055ee9ea43b

-- Generated from openai/math@1581d4c lean/OAI/Analysis/C0Absorption/Localization.lean:L104-L143
-- (upload_full_project.md Phase 4): solution for node OAI.C0Absorption.disjoint_supports_signed_lipschitz. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_C0Absorption
import Definitions.Def_OAI_Analysis_C0Absorption_Molecules
import Definitions.Def_OAI_Analysis_C0Absorption_Norm
import Definitions.Def_OAI_Analysis_C0Absorption_Completion
import Definitions.Def_OAI_Analysis_C0Absorption_Signs
import Definitions.Def_OAI_Analysis_C0Absorption_Lists
import Definitions.Def_OAI_Analysis_C0Absorption_Pairings
import Definitions.Def_OAI_Analysis_C0Absorption_Localization
import Theorems.Thm_OAI_C0Absorption_lipschitz_convex_subtype_of_local

-- ---- from OAI.Analysis.C0Absorption.Localization ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace C0Absorption

open scoped BigOperators NNReal ENNReal
noncomputable section
open Finset

open Set Filter Topology

theorem eventually_zero_of_not_tsupport {X : Type*} [TopologicalSpace X]
    {f : X → ℝ} {x : X} (hx : x ∉ tsupport f) : ∀ᶠ y in nhds x, f y = 0 := by
  filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hx] with y hy
  exact image_eq_zero_of_notMem_tsupport hy

theorem disjoint_supports_signed_lipschitz {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {B : Set E} (hB : Convex ℝ B)
    {ι : Type*} [Fintype ι] (f : ι → B → ℝ) (K : ℝ≥0)
    (hf : ∀ i, LipschitzWith K (f i))
    (hdisj : Pairwise (fun i j => Disjoint (tsupport (f i)) (tsupport (f j))))
    (ε : ι → ℝ) (hε : ∀ i, |ε i| = 1) :
    LipschitzWith K (fun x => ∑ i, ε i * f i x) := by
  classical
  apply lipschitz_convex_subtype_of_local hB
  · exact continuous_finsetSum _ (fun i _ => continuous_const.mul (hf i).continuous)
  intro x
  by_cases hex : ∃ j, x ∈ tsupport (f j)
  · obtain ⟨j, hj⟩ := hex
    have hz : ∀ i, i ≠ j → ∀ᶠ y in nhds x, f i y = 0 := by
      intro i hij
      apply eventually_zero_of_not_tsupport
      intro hi
      exact Set.disjoint_left.mp (hdisj hij) hi hj
    have he : ∀ᶠ y in nhds x, ∀ i, i ≠ j → f i y = 0 :=
      Filter.eventually_all.mpr (fun i => if hi : i = j then by simp [hi] else
        (hz i hi).mono (fun y hy _ => hy))
    filter_upwards [he] with y hy
    have hx (i) (hi : i ≠ j) : f i x = 0 := (hz i hi).self_of_nhds
    have sx : (∑ i, ε i * f i x) = ε j * f j x := by
      apply Finset.sum_eq_single j
      · intro i hi hij; simp [hx i hij]
      · simp
    have sy : (∑ i, ε i * f i y) = ε j * f j y := by
      apply Finset.sum_eq_single j
      · intro i hi hij; simp [hy i hij]
      · simp
    rw [sx, sy, Real.dist_eq, ← mul_sub, abs_mul, hε, one_mul, ← Real.dist_eq]
    exact (hf j).dist_le_mul x y
  · push Not at hex
    have he : ∀ᶠ y in nhds x, ∀ i, f i y = 0 :=
      Filter.eventually_all.mpr (fun i => eventually_zero_of_not_tsupport (hex i))
    filter_upwards [he] with y hy
    have hx (i) : f i x = 0 := image_eq_zero_of_notMem_tsupport (hex i)
    simp only [hx, hy, mul_zero, Finset.sum_const_zero, dist_self]
    positivity

noncomputable section

end

end
end C0Absorption

end OAI

-- ---- platform node ----
open OAI OAI.C0Absorption
open scoped BigOperators NNReal ENNReal
open Finset
open Set Filter Topology


theorem solution : type_of% @_root_.OAI.C0Absorption.disjoint_supports_signed_lipschitz := @_root_.OAI.C0Absorption.disjoint_supports_signed_lipschitz
