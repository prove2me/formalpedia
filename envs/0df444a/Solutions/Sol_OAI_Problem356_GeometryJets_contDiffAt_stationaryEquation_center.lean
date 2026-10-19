-- Prove2me | solution 1 for OAI.Problem356.GeometryJets.contDiffAt_stationaryEquation_center
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:01:44.718642+00:00
-- url     : https://prove2.me/submissions/2bac29a7-5b27-40eb-b252-2b05ddf9a3d8

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/StationaryEquation.lean:L113-L127
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.GeometryJets.contDiffAt_stationaryEquation_center. The node keeps its source
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

-- ---- from OAI.Analysis.CoulombTransport.CoulombCalculus ----
namespace OAI

universe uE

noncomputable section

open scoped RealInnerProductSpace

namespace Problem356.CoulombCalculus

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma contDiffAt_pairGradient {n : WithTop ENat} {x : E} (hx : x ≠ 0) :
    ContDiffAt ℝ n (pairGradient : E → E) x := by
  exact (((contDiffAt_norm ℝ hx).pow 3).inv
    (pow_ne_zero 3 (norm_ne_zero_iff.mpr hx))).neg.smul contDiffAt_id

end Problem356.CoulombCalculus

end

end OAI

-- ---- from OAI.Analysis.CoulombTransport.GeometryJets ----
namespace OAI

universe uE

noncomputable section

open scoped RealInnerProductSpace

namespace Problem356.GeometryJets

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
theorem center_nonzero {a : E} (ha : ‖a‖ = 1) : a ≠ 0 := by
  intro h
  simp [h] at ha

end Problem356.GeometryJets

end

end OAI

-- ---- from OAI.Analysis.CoulombTransport.StationaryEquation ----
namespace OAI

universe uE

noncomputable section

namespace Problem356.GeometryJets

open CoulombCalculus

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma contDiffAt_stationaryEquation {n : WithTop ENat} (K : ℝ) (a : E)
    (p : E × (E × E)) (hxy : p.2.1 ≠ p.1) (hxz : p.2.1 ≠ p.2.2)
    (hyz : p.1 ≠ p.2.2) : ContDiffAt ℝ n (stationaryEquation K a) p := by
  have hy : ContDiffAt ℝ n (fun q : E × (E × E) => q.1) p := contDiffAt_fst
  have hx : ContDiffAt ℝ n (fun q : E × (E × E) => q.2.1) p := contDiffAt_snd.fst
  have hz : ContDiffAt ℝ n (fun q : E × (E × E) => q.2.2) p := contDiffAt_snd.snd
  have h1 := (contDiffAt_pairGradient (n := n) (sub_ne_zero.mpr hxy)).comp p (hx.sub hy)
  have h2 := (contDiffAt_pairGradient (n := n) (sub_ne_zero.mpr hxz)).comp p (hx.sub hz)
  have h3 := (contDiffAt_pairGradient (n := n) (sub_ne_zero.mpr hyz)).comp p (hy.sub hz)
  exact ((h1.add h2).add (hx.const_smul K)).prodMk
    (((h2.neg.sub h3).sub contDiffAt_const).add ((hz.add contDiffAt_const).const_smul K))

lemma contDiffAt_stationaryEquation_center {n : WithTop ENat}
    (K : ℝ) (a : E) (ha : ‖a‖ = 1) :
    ContDiffAt ℝ n (stationaryEquation K a) (a, (0, -a)) := by
  have ha0 := center_nonzero ha
  apply contDiffAt_stationaryEquation
  · exact ha0.symm
  · exact (neg_ne_zero.mpr ha0).symm
  · intro h
    have hnorm : ‖a - -a‖ = 2 := by
      have hvec : a - -a = (2 : ℝ) • a := by module
      rw [hvec, norm_smul, ha]
      norm_num
    change a = -a at h
    rw [sub_eq_zero.mpr h, norm_zero] at hnorm
    norm_num at hnorm

end Problem356.GeometryJets

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem356 OAI.Problem356.GeometryJets
open CoulombCalculus


theorem solution.{uE} : type_of% @_root_.OAI.Problem356.GeometryJets.contDiffAt_stationaryEquation_center.{uE} := @_root_.OAI.Problem356.GeometryJets.contDiffAt_stationaryEquation_center.{uE}
