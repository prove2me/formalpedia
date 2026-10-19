-- Prove2me | solution 1 for OAI.Release075.exists_finite_preserving_rectangles
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T08:59:30.330593+00:00
-- url     : https://prove2.me/submissions/1fcfd66b-7528-413a-9829-aeab050f8278

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/MatrixRank.lean:L902-L919
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.exists_finite_preserving_rectangles. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank

-- ---- from OAI.GroupTheory.Hyperbolic.MatrixRank ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace Release075

universe u v

open scoped BigOperators

/-- Finite separating families can be combined into one finite target. -/
theorem exists_finite_separating_family {G : Type u} {ι : Type v} [Group G] [Fintype ι]
    [Group.ResiduallyFinite G] (w : ι → G) (hw : ∀ i, w i ≠ 1) :
    ∃ (Q : Type (max u v)) (_ : Group Q) (_ : Fintype Q) (φ : G →* Q), ∀ i, φ (w i) ≠ 1 := by
  classical
  choose H hH using fun i => Group.exists_finiteIndexNormalSubgroup_notMem (w i) (hw i)
  let Q := ∀ i, G ⧸ (H i).toSubgroup
  let : ∀ i, Fintype (G ⧸ (H i).toSubgroup) := fun i => Fintype.ofFinite _
  let φ : G →* Q := MonoidHom.pi (fun i => QuotientGroup.mk' (H i).toSubgroup)
  refine ⟨Q, inferInstance, inferInstance, φ, ?_⟩
  intro i hi
  have h := congrFun hi i
  exact hH i ((QuotientGroup.eq_one_iff (w i)).mp h)

/-- All specified nontrivial rectangular words can be preserved in one finite
image if the group is residually finite. -/
theorem exists_finite_preserving_rectangles {I : Type u} {G : Type v} [Fintype I] [Group G]
    [Group.ResiduallyFinite G] {r : ℕ} (g : I → Fin r → Fin r → G)
    (hg : ∀ i, RectanglesSurvive (g i)) :
    ∃ (Q : Type (max u v)) (_ : Group Q) (_ : Fintype Q) (φ : G →* Q),
      ∀ i, RectanglesSurvive (fun u v => φ (g i u v)) := by
  classical
  let J := {x : I × Fin r × Fin r × Fin r × Fin r // x.2.1 ≠ x.2.2.1 ∧ x.2.2.2.1 ≠ x.2.2.2.2}
  let w : J → G := fun x => g x.val.1 x.val.2.1 x.val.2.2.2.1 *
    (g x.val.1 x.val.2.2.1 x.val.2.2.2.1)⁻¹ *
    g x.val.1 x.val.2.2.1 x.val.2.2.2.2 * (g x.val.1 x.val.2.1 x.val.2.2.2.2)⁻¹
  have hw (x : J) : w x ≠ 1 := hg _ _ _ _ _ x.property.1 x.property.2
  obtain ⟨Q,hQ,hfin,φ,hφ⟩ := exists_finite_separating_family w hw
  refine ⟨Q,hQ,hfin,φ,?_⟩
  intro i u u' v v' hu hv
  have h := hφ ⟨(i,u,u',v,v'),hu,hv⟩
  simpa [w] using h

end Release075

end OAI

-- ---- platform node ----
open OAI OAI.Release075
open scoped BigOperators


theorem solution.{u,v} : type_of% @_root_.OAI.Release075.exists_finite_preserving_rectangles.{u,v} := @_root_.OAI.Release075.exists_finite_preserving_rectangles.{u,v}
