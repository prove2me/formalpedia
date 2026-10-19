-- Prove2me | solution 2 for OAI.Problem356.strictConvexOn_of_line_deriv2_pos
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:14:17.227983+00:00
-- url     : https://prove2.me/submissions/f6c9312b-ca21-486e-971f-cbb02a45e392

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/StrictMinimum.lean:L50-L74
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.strictConvexOn_of_line_deriv2_pos. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CoulombCounterexample
import Definitions.Def_OAI_Analysis_CoulombTransport_AxisHessian
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchCoupling
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombEstimates
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchSeparation
import Definitions.Def_OAI_Analysis_CoulombTransport_GraphBridge
import Definitions.Def_OAI_Analysis_CoulombTransport_DualCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_OptimalLocalization
import Definitions.Def_OAI_Analysis_CoulombTransport_Calibration
import Definitions.Def_OAI_Analysis_CoulombTransport_CertificateAttainment
import Definitions.Def_OAI_Analysis_CoulombTransport_SplitMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_PartitionLabel
import Definitions.Def_OAI_Analysis_CoulombTransport_CenterCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_CommonBranches
import Definitions.Def_OAI_Analysis_CoulombTransport_DensityMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_ComponentPotential
import Definitions.Def_OAI_Analysis_CoulombTransport_LocalImplicit
import Definitions.Def_OAI_Analysis_CoulombTransport_HessianCLM
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombCalculus
import Definitions.Def_OAI_Analysis_CoulombTransport_StationaryEquation
import Definitions.Def_OAI_Analysis_CoulombTransport_HessianMatrix
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombCoercivity

-- ---- from OAI.Analysis.CoulombTransport.StrictMinimum ----
namespace OAI

universe uE uP

noncomputable section

open Set Filter
open scoped Topology

namespace Problem356

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Strict positivity of second derivatives on nonconstant line segments implies
strict convexity in an arbitrary real normed space. -/
theorem strictConvexOn_of_line_deriv2_pos {s : Set E} {f : E → ℝ}
    (hs : Convex ℝ s) (hf : ContinuousOn f s)
    (hpos : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → ∀ t ∈ Ioo (0 : ℝ) 1,
      0 < deriv (deriv (f ∘ AffineMap.lineMap x y)) t) :
    StrictConvexOn ℝ s f := by
  refine ⟨hs, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hmaps : MapsTo (AffineMap.lineMap x y) (Icc (0 : ℝ) 1) s := by
    intro t ht
    rw [AffineMap.lineMap_apply_module]
    exact hs hx hy (sub_nonneg.mpr ht.2) ht.1 (by ring)
  have hcont : ContinuousOn (f ∘ AffineMap.lineMap x y) (Icc (0 : ℝ) 1) :=
    hf.comp (AffineMap.lineMap x y : ℝ →ᵃ[ℝ] E).differentiable.continuous.continuousOn hmaps
  have hstrict : StrictConvexOn ℝ (Icc (0 : ℝ) 1)
      (f ∘ AffineMap.lineMap x y) := by
    apply strictConvexOn_of_deriv2_pos (convex_Icc _ _) hcont
    intro t ht
    exact hpos x hx y hy hxy t (by simpa using ht)
  have hh := hstrict.2 (by simp : (0 : ℝ) ∈ Icc (0 : ℝ) 1)
    (by simp : (1 : ℝ) ∈ Icc (0 : ℝ) 1) (by norm_num : (0 : ℝ) ≠ 1)
    ha hb hab
  have ha1 : 1 - b = a := by linarith
  simpa [AffineMap.lineMap_apply_module, ha1] using hh

end Problem356

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem356
open Set Filter
open scoped Topology


theorem solution.{uE} : type_of% @_root_.OAI.Problem356.strictConvexOn_of_line_deriv2_pos.{uE} := @_root_.OAI.Problem356.strictConvexOn_of_line_deriv2_pos.{uE}
