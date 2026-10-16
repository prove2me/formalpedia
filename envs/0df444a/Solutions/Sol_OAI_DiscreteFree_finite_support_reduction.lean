-- Prove2me | solution 1 for OAI.DiscreteFree.finite_support_reduction
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T10:37:03.177086+00:00
-- url     : https://prove2.me/submissions/d27184eb-62b3-4e21-85a3-e447cf5e6bab

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzFree/SupportReduction.lean:L63-L100
-- (upload_full_project.md Phase 4): solution for node OAI.DiscreteFree.finite_support_reduction. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DiscreteLipschitzFree
import Definitions.Def_OAI_Analysis_LipschitzFree_PortGraphs
import Definitions.Def_OAI_Analysis_LipschitzFree_RenormingModel
import Definitions.Def_OAI_Analysis_LipschitzFree_Model
import Definitions.Def_OAI_Analysis_LipschitzFree_Parameters
import Definitions.Def_OAI_Analysis_LipschitzFree_BoxLabels
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricClosure
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricBlock
import Definitions.Def_OAI_Analysis_LipschitzFree_Attachment
import Definitions.Def_OAI_Analysis_LipschitzFree_Words
import Definitions.Def_OAI_Analysis_LipschitzFree_StatePaths
import Definitions.Def_OAI_Analysis_LipschitzFree_SignedTests
import Definitions.Def_OAI_Analysis_LipschitzFree_GraphWalks
import Definitions.Def_OAI_Analysis_LipschitzFree_Evaluation
import Definitions.Def_OAI_Analysis_LipschitzFree_Coordinates
import Theorems.Thm_OAI_DiscreteFree_projection_compact

-- ---- from OAI.Analysis.LipschitzFree.Coordinates ----
namespace OAI

/-!
# Signed evaluation coefficients and finite-support projections
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree
open scoped BigOperators Classical
variable {M : Type*} [MetricSpace M] (o : M)

namespace Lip0
end Lip0

variable (sep : ∀ x y : M, x ≠ y → 1 ≤ dist x y)

omit [MetricSpace M] in
theorem sum_point_test {V : Type*} [AddCommMonoid V] (F : Finset M) (x : M) (v : M → V) :
    (∑ j ∈ F, if x = j ∧ j ≠ o then v j else 0) = if x ∈ F ∧ x ≠ o then v x else 0 := by
  have ht (j : M) : (if x = j ∧ j ≠ o then v j else 0) =
      if j = x then (if x ≠ o then v x else 0) else 0 := by
    by_cases h : j = x
    · subst j; simp
    · simp [h, Ne.symm h]
  simp_rw [ht]
  rw [Finset.sum_ite_eq']
  split_ifs <;> simp_all

theorem supportProjection_delta (F : Finset M) (x : M) :
    supportProjection o sep F (delta o x) = if x ∈ F then delta o x else 0 := by
  rw [supportProjection_apply]
  by_cases hx : x = o
  · subst x
    simp
  · simp only [coordinate_delta, ite_smul, one_smul, zero_smul]
    rw [sum_point_test]
    simp [hx]

end DiscreteFree
end

end

end OAI

-- ---- from OAI.Analysis.LipschitzFree.CompactApproximation ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Compact-uniform approximation on bounded separated spaces
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree
open scoped BigOperators Classical
variable {M : Type*} [MetricSpace M] (o : M)

variable (sep : ∀ x y : M, x ≠ y → 1 ≤ dist x y)

theorem supportProjection_range (F : Finset M) :
    LinearMap.range (supportProjection o sep F).toLinearMap ≤
      Submodule.span ℝ ((delta o) '' (F : Set M)) := by
  rintro u ⟨v, rfl⟩
  change supportProjection o sep F v ∈ _
  rw [supportProjection_apply]
  exact Submodule.sum_mem _ (fun j hj => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨j, hj, rfl⟩))

theorem supportProjection_finiteRank (F : Finset M) :
    Module.Finite ℝ (LinearMap.range (supportProjection o sep F).toLinearMap) :=
  (Submodule.fg_iff_finiteDimensional _).mp
    ((Submodule.fg_span (F.finite_toSet.image (delta o))).of_le (supportProjection_range o sep F))

variable (B : ℝ) (hB : 0 ≤ B) (hb : ∀ x, dist x o ≤ B)

end DiscreteFree
end

end

end OAI

-- ---- from OAI.Analysis.LipschitzFree.SupportReduction ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e

namespace OAI

/-!
# Finite-rank operators admit finite-support perturbations
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree
open scoped BigOperators Classical
variable {M : Type*} [MetricSpace M] (o : M)
    (sep : ∀ x y : M, x ≠ y → 1 ≤ dist x y)

theorem projection_span_fixed (F : Finset M) {u : FreeSpace o}
    (hu : u ∈ Submodule.span ℝ ((delta o) '' (F : Set M))) :
    supportProjection o sep F u = u := by
  induction hu using Submodule.span_induction with
  | mem u h =>
    obtain ⟨x, hx, rfl⟩ := h
    rw [supportProjection_delta, ite_eq_left (show x ∈ F from hx)]
  | zero => exact map_zero _
  | add x y hx hy ihx ihy => rw [map_add, ihx, ihy]
  | smul c x hx ih => rw [map_smul, ih]

theorem projection_idempotent (F : Finset M) (u : FreeSpace o) :
    supportProjection o sep F (supportProjection o sep F u) = supportProjection o sep F u :=
  projection_span_fixed o sep F (supportProjection_range o sep F ⟨u, rfl⟩)

theorem projection_comp_finiteRank (F : Finset M) (T : FreeSpace o →L[ℝ] FreeSpace o) :
    Module.Finite ℝ (LinearMap.range ((supportProjection o sep F).comp T).toLinearMap) := by
  have := supportProjection_finiteRank o sep F
  exact Module.Finite.of_injective
    (Submodule.inclusion (LinearMap.range_comp_le_range T.toLinearMap (supportProjection o sep F).toLinearMap))
    (Submodule.inclusion_injective _)

theorem projection_finiteRank_approx (B : ℝ) (hB : 0 ≤ B) (hb : ∀ x, dist x o ≤ B)
    (T : FreeSpace o →L[ℝ] FreeSpace o)
    (hT : Module.Finite ℝ (LinearMap.range T.toLinearMap)) (ε : ℝ) (hε : 0 < ε) :
    ∃ F : Finset M, ∀ G : Finset M, F ⊆ G → ‖(supportProjection o sep G).comp T - T‖ < ε := by
  let Y := LinearMap.range T.toLinearMap
  let J : Y →L[ℝ] FreeSpace o := Y.subtypeL
  let C : Set (FreeSpace o) := J '' Metric.closedBall (0 : Y) ‖T‖
  have hC : IsCompact C := (isCompact_closedBall (0 : Y) ‖T‖).image J.continuous
  obtain ⟨F, hF⟩ := projection_compact o sep B hB hb C hC (ε/2) (by positivity)
  refine ⟨F, fun G hG => ?_⟩
  have hnorm : ‖(supportProjection o sep G).comp T - T‖ ≤ ε/2 := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro u hu
    have hTu : T u ∈ C := by
      refine ⟨⟨T u, ⟨u, rfl⟩⟩, ?_, rfl⟩
      change dist (T u) 0 ≤ ‖T‖
      simpa only [dist_zero_right, hu, mul_one] using T.le_opNorm u
    exact (hF G hG (T u) hTu).le
  linarith

theorem finite_support_reduction (B p : ℝ) (hB : 0 ≤ B) (hp : 1 ≤ p)
    (hb : ∀ x, dist x o ≤ B) (A : Finset M)
    (T₀ : FreeSpace o →L[ℝ] FreeSpace o)
    (hfinite : Module.Finite ℝ (LinearMap.range T₀.toLinearMap)) (hnorm : ‖T₀‖ ≤ p)
    (hanchor : ∀ a ∈ A, ‖T₀ (delta o a) - delta o a‖ < 1/2) :
    ∃ (S : Finset M) (T : FreeSpace o →L[ℝ] FreeSpace o), o ∈ S ∧
      Module.Finite ℝ (LinearMap.range T.toLinearMap) ∧ ‖T‖ ≤ 2*p ∧
      (∀ u, supportProjection o sep S (T u) = T u) ∧
      ∀ a ∈ A, ‖T (delta o a) - delta o a‖ < 1 := by
  let ε := min p (1/(2*(B+1)))
  have hε : 0 < ε := lt_min (by linarith) (by positivity)
  obtain ⟨F, hF⟩ := projection_finiteRank_approx o sep B hB hb T₀ hfinite ε hε
  let S := insert o F
  let T := (supportProjection o sep S).comp T₀
  have hdiff : ‖T-T₀‖ < ε := hF S (Finset.subset_insert _ _)
  have hn : ‖T‖ ≤ 2*p := by
    have hs := norm_add_le (T-T₀) T₀
    rw [sub_add_cancel] at hs
    have hεp : ε ≤ p := min_le_left _ _
    linarith
  refine ⟨S, T, Finset.mem_insert_self _ _, projection_comp_finiteRank o sep S T₀,
    hn, fun u => projection_idempotent o sep S (T₀ u), fun a ha => ?_⟩
  have hda := delta_norm o a
  have he : ‖(T-T₀) (delta o a)‖ ≤ ε*B := by
    calc
      _ ≤ ‖T-T₀‖ * ‖delta o a‖ := (T-T₀).le_opNorm _
      _ ≤ ε * B := mul_le_mul hdiff.le (by simpa using hb a) (norm_nonneg _) hε.le
  have hfrac : ε*B < 1/2 := by
    have hh : ε ≤ 1/(2*(B+1)) := min_le_right _ _
    have hden : 0 < 2*(B+1) := by positivity
    have hmul := (le_div_iff₀ hden).mp hh
    nlinarith
  calc
    ‖T (delta o a) - delta o a‖ =
      ‖(T-T₀) (delta o a) + (T₀ (delta o a) - delta o a)‖ := by
        simp only [sub_apply]; congr 1; abel
    _ ≤ ‖(T-T₀) (delta o a)‖ + ‖T₀ (delta o a) - delta o a‖ := norm_add_le _ _
    _ < 1 := by linarith [hanchor a ha]

end DiscreteFree
end

end

end OAI

-- ---- platform node ----
open OAI OAI.DiscreteFree
open scoped BigOperators ENNReal
open scoped BigOperators Classical


theorem solution : type_of% @_root_.OAI.DiscreteFree.finite_support_reduction := @_root_.OAI.DiscreteFree.finite_support_reduction
