-- Prove2me | solution 1 for OAI.PermanentBorder.Multigraded.bilinear_simple_point_count_multichart
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:39:19.067153+00:00
-- url     : https://prove2.me/submissions/f90f4d92-ded3-4509-9a21-6d92a0c1c57a

-- Generated from openai/math@1581d4c lean/OAI/Algebra/Determinantal/ProjectiveCounts.lean:L378-L415
-- (upload_full_project.md Phase 4): solution for node OAI.PermanentBorder.Multigraded.bilinear_simple_point_count_multichart. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SmoothInitialForm
import Definitions.Def_OAI_Algebra_Determinantal_Multigraded
import Definitions.Def_OAI_Algebra_Determinantal_LinearForms
import Definitions.Def_OAI_Algebra_Determinantal_PointBounds
import Definitions.Def_OAI_Algebra_Determinantal_ProjectiveCounts
import Theorems.Thm_OAI_PermanentBorder_Multigraded_product_simple_point_bound_multichart

-- ---- from OAI.Algebra.Determinantal.ProjectiveCounts ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI
namespace PermanentBorder.Multigraded
open MvPolynomial
section BilinearPointCount
variable {ι L : Type*} [Fintype ι] [DecidableEq ι] [Fintype L] [DecidableEq L]

end BilinearPointCount
end PermanentBorder.Multigraded
namespace PermanentBorder.Multigraded
open MvPolynomial
section ProductAffineChart
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable {L : Type*} [Fintype L] [DecidableEq L]

end ProductAffineChart
end PermanentBorder.Multigraded
namespace PermanentBorder.Multigraded
open MvPolynomial
section ProjectiveInterpolation
variable {K σ ι L : Type*} [Field K] [Fintype ι] [DecidableEq ι]

variable [Fintype L] [DecidableEq L]

end ProjectiveInterpolation
end PermanentBorder.Multigraded
namespace PermanentBorder.Multigraded
open MvPolynomial
section ProjectivePointBound
variable {K σ ι L : Type*} [Field K] [Fintype σ] [Fintype ι] [DecidableEq ι]
  [Fintype L] [DecidableEq L]

end ProjectivePointBound
end PermanentBorder.Multigraded
namespace PermanentBorder.Multigraded
open MvPolynomial Filter
open scoped Topology
section MultiChartProductCount
variable {ι L V : Type*} [Fintype ι] [DecidableEq ι] [Fintype L] [DecidableEq L]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

end MultiChartProductCount
end PermanentBorder.Multigraded
namespace PermanentBorder.Multigraded
open MvPolynomial
section BilinearMultiChartCount
variable {ι L V : Type*} [Fintype ι] [DecidableEq ι] [Fintype L] [DecidableEq L]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

theorem bilinear_simple_point_count_multichart (a : ι →₀ ℕ) {M : ℕ}
    (u v : Fin M → ι) (hM : M = ∑ j, a j)
    (F : Fin M → MvPolynomial (BlockVariables a) ℂ)
    (hF : ∀ i, (F i).IsWeightedHomogeneous
      (blockWeight (fun v : BlockVariables a => v.1))
      (Pi.single (u i) 1 + Pi.single (v i) 1))
    (base : L → ι → BlockVariables a) (hbase : ∀ i j, (base i j).1 = j)
    (e : L → (Fin M → ℂ) ≃L[ℂ] V)
    (chart : L → V → BlockVariables a → ℂ) (hc : ∀ i, ContDiff ℂ 1 (chart i))
    (hcn : ∀ i z j, chart i z (base i j) = 1)
    (x : L → V)
    (hx : ∀ i j, i ≠ j → BlockSeparated (fun v : BlockVariables a => v.1)
      (chart i (x i)) (chart j (x j)))
    (hz : ∀ i j, eval (chart i (x i)) (F j) = 0)
    (hs : ∀ i, (fderiv ℂ (fun z => e i (fun j => eval (chart i z) (F j)))
      (x i)).IsInvertible) :
    Fintype.card L ≤ (mixedPolynomial u v).coeff a := by
  classical
  let t : (Fin M × Bool) → ℂ := fun i =>
    Infinite.natEmbedding ℂ ((Fintype.equivFin (Fin M × Bool) i).val)
  have ht : Function.Injective t :=
    (Infinite.natEmbedding ℂ).injective.comp
      (Fin.val_injective.comp (Fintype.equivFin (Fin M × Bool)).injective)
  generalize hqs : List.ofFn (vandermondePairs a u v t) = qs
  have hlen : qs.length = M := by rw [← hqs, List.length_ofFn]
  cases hlen
  have hget (i : Fin qs.length) : qs.get i = vandermondePairs a u v t i := by
    have h := congrArg (fun l => l[i.val]?) hqs
    simpa only [List.getElem?_ofFn, dite_eq_left i.isLt, List.getElem?_eq_getElem i.isLt,
      Option.some.injEq, List.get_eq_getElem] using h.symm
  apply product_simple_point_bound_multichart a qs u v t ht
    (fun i => by rw [hget]; rfl) (fun i => by rw [hget]; rfl) ?_ hM F
    (by intro i; simpa only [hget, vandermondePairs] using hF i)
    base hbase e chart hc hcn x hx hz hs
  intro q hq j
  rw [← hqs] at hq
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
  by_cases hj : j = u i <;> simp [vandermondePairs, hj]

end BilinearMultiChartCount
end PermanentBorder.Multigraded

end OAI

-- ---- platform node ----
open OAI OAI.PermanentBorder OAI.PermanentBorder.Multigraded
open MvPolynomial


theorem solution : type_of% @_root_.OAI.PermanentBorder.Multigraded.bilinear_simple_point_count_multichart := @_root_.OAI.PermanentBorder.Multigraded.bilinear_simple_point_count_multichart
