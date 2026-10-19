-- Prove2me | solution 2 for OAI.Problem356.strictConvexOn_of_positive_hessian
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:15:56.857649+00:00
-- url     : https://prove2.me/submissions/add6ad6f-c47a-42d2-a6b2-6314532611b9

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/StrictMinimum.lean:L76-L105
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.strictConvexOn_of_positive_hessian. The node keeps its source
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
import Theorems.Thm_OAI_Problem356_strictConvexOn_of_line_deriv2_pos

-- ---- from OAI.Analysis.CoulombTransport.StrictMinimum ----
namespace OAI

universe uE uP

noncomputable section

open Set Filter
open scoped Topology

namespace Problem356

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A positive-definite second Fréchet derivative gives strict convexity on an
open convex domain. The two derivative fields are explicit, so this applies
directly to computed Hessians without rewriting `fderiv`. -/
theorem strictConvexOn_of_positive_hessian {s : Set E} {f : E → ℝ}
    {f' : E → E →L[ℝ] ℝ} {f'' : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hs : Convex ℝ s) (hsopen : IsOpen s)
    (hf : ∀ z ∈ s, HasFDerivAt f (f' z) z)
    (hf' : ∀ z ∈ s, HasFDerivAt f' (f'' z) z)
    (hpos : ∀ z ∈ s, ∀ v : E, v ≠ 0 → 0 < f'' z v v) :
    StrictConvexOn ℝ s f := by
  apply strictConvexOn_of_line_deriv2_pos hs
    (fun z hz => (hf z hz).continuousAt.continuousWithinAt)
  intro x hx y hy hxy t ht
  have hmaps : MapsTo (AffineMap.lineMap x y) (Icc (0 : ℝ) 1) s := by
    intro u hu
    rw [AffineMap.lineMap_apply_module]
    exact hs hx hy (sub_nonneg.mpr hu.2) hu.1 (by ring)
  have hz : AffineMap.lineMap x y t ∈ s := hmaps ⟨ht.1.le, ht.2.le⟩
  have hnear : ∀ᶠ u in 𝓝 t, AffineMap.lineMap x y u ∈ s :=
    AffineMap.lineMap_continuous.continuousAt.eventually_mem (hsopen.mem_nhds hz)
  have hfirst : deriv (f ∘ AffineMap.lineMap x y) =ᶠ[𝓝 t]
      (fun u => f' (AffineMap.lineMap x y u) (y - x)) := by
    filter_upwards [hnear] with u hu
    exact ((hf _ hu).comp_hasDerivAt u AffineMap.hasDerivAt_lineMap).deriv
  have hsecond : HasDerivAt (fun u : ℝ => f' (AffineMap.lineMap x y u) (y - x))
      (f'' (AffineMap.lineMap x y t) (y - x) (y - x)) t := by
    have hcomp := (hf' _ hz).comp_hasDerivAt t AffineMap.hasDerivAt_lineMap
    simpa using hcomp.clm_apply (hasDerivAt_const t (y - x))
  rw [hfirst.deriv_eq, hsecond.deriv]
  exact hpos _ hz (y - x) (sub_ne_zero.mpr hxy.symm)

end Problem356

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem356
open Set Filter
open scoped Topology


theorem solution.{uE} : type_of% @_root_.OAI.Problem356.strictConvexOn_of_positive_hessian.{uE} := @_root_.OAI.Problem356.strictConvexOn_of_positive_hessian.{uE}
