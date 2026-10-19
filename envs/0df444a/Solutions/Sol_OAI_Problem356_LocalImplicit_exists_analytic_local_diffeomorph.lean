-- Prove2me | solution 1 for OAI.Problem356.LocalImplicit.exists_analytic_local_diffeomorph
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:55:31.76034+00:00
-- url     : https://prove2.me/submissions/b7bfb541-4fb0-4c58-8dca-ba65a49c166d

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/LocalImplicit.lean:L56-L96
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.LocalImplicit.exists_analytic_local_diffeomorph. The node keeps its source
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

-- ---- from OAI.Analysis.CoulombTransport.LocalImplicit ----
namespace OAI

universe uP uS

noncomputable section

open Filter Set
open scoped Topology ContDiff

namespace Problem356.LocalImplicit

variable {P : Type uP} {S : Type uS}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]

omit [CompleteSpace S] in
/-- A map analytic at one point with invertible derivative is analytic in both
 directions on a suitable open partial homeomorphism. -/
theorem exists_analytic_local_diffeomorph
    (f : P → S) (p : P)
    (hf : ContDiffAt ℝ ω f p)
    (hinv : (fderiv ℝ f p).IsInvertible) :
    ∃ e : OpenPartialHomeomorph P S,
      (e : P → S) = f ∧ p ∈ e.source ∧
      ContDiffOn ℝ ω e e.source ∧ ContDiffOn ℝ ω e.symm e.target := by
  obtain ⟨A, hA⟩ := hinv
  have hderiv : HasFDerivAt f (A : P →L[ℝ] S) p := by
    rw [hA]
    exact (hf.differentiableAt (by simp)).hasFDerivAt
  let e₀ := hf.toOpenPartialHomeomorph f hderiv (by simp)
  have he₀ : (e₀ : P → S) = f := rfl
  have hp₀ : p ∈ e₀.source := hf.mem_toOpenPartialHomeomorph_source hderiv (by simp)
  have hfp₀ : f p ∈ e₀.target := hf.image_mem_toOpenPartialHomeomorph_target hderiv (by simp)
  have hinverse : ContDiffAt ℝ ω e₀.symm (f p) := by
    have hleft : e₀.symm (f p) = p := e₀.left_inv hp₀
    apply e₀.contDiffAt_symm hfp₀
    · simpa only [hleft, he₀] using hderiv
    · simpa only [hleft, he₀] using hf
  obtain ⟨V, hVsub, hVopen, hfpV⟩ :=
    mem_nhds_iff.mp (hinverse.eventually (by simp))
  have hpre : f ⁻¹' V ∈ 𝓝 p := hf.continuousAt.preimage_mem_nhds (hVopen.mem_nhds hfpV)
  obtain ⟨U, hUsub, hUopen, hpU⟩ := mem_nhds_iff.mp
    (inter_mem (e₀.open_source.mem_nhds hp₀) (inter_mem (hf.eventually (by simp)) hpre))
  refine ⟨e₀.restrOpen U hUopen, rfl, ⟨hp₀, hpU⟩, ?_, ?_⟩
  · apply (e₀.restrOpen U hUopen).open_source.contDiffOn_iff.mpr
    intro x hx
    exact (hUsub hx.2).2.1
  · apply (e₀.restrOpen U hUopen).open_target.contDiffOn_iff.mpr
    intro y hy
    have hx := (e₀.restrOpen U hUopen).map_target hy
    have hxy := (e₀.restrOpen U hUopen).right_inv hy
    apply hVsub
    have hmem := (hUsub hx.2).2.2
    change f ((e₀.restrOpen U hUopen).symm y) ∈ V at hmem
    change f ((e₀.restrOpen U hUopen).symm y) = y at hxy
    exact hxy ▸ hmem

namespace AnalyticStationaryCharts

variable {G : P × (S × S) → S × S} {p : P} {s : S × S}

omit [CompleteSpace P] [CompleteSpace S]

end AnalyticStationaryCharts

end Problem356.LocalImplicit

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem356 OAI.Problem356.LocalImplicit
open Filter Set
open scoped Topology ContDiff


theorem solution.{uP,uS} : type_of% @_root_.OAI.Problem356.LocalImplicit.exists_analytic_local_diffeomorph.{uP,uS} := @_root_.OAI.Problem356.LocalImplicit.exists_analytic_local_diffeomorph.{uP,uS}
