-- Prove2me | solution 1 for OAI.Problem356.LocalGeometry.nonempty_localSupportingCharts
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:22:01.622984+00:00
-- url     : https://prove2.me/submissions/fb9b4bf9-f545-4f2a-8022-6add6b0383e0

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/LocalCertificate.lean:L38-L143
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.LocalGeometry.nonempty_localSupportingCharts. The node keeps its source
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
import Definitions.Def_OAI_Analysis_CoulombTransport_LocalCertificate
import Theorems.Thm_OAI_Problem356_bilinear_coercive_of_norm_sub_le
import Theorems.Thm_OAI_Problem356_convex_isMinOn_of_hasFDerivAt_zero
import Theorems.Thm_OAI_Problem356_exists_bilinear_coercivity_of_pos
import Theorems.Thm_OAI_Problem356_strictConvexOn_of_positive_hessian
import Theorems.Thm_OAI_Problem356_strictConvex_eq_iff_of_hasFDerivAt_zero

-- ---- from OAI.Analysis.CoulombTransport.StrictMinimum ----
namespace OAI

universe uE uP

noncomputable section

open Set Filter
open scoped Topology

namespace Problem356

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A smooth stationary branch in strictly convex state slices defines a smooth
supporting value, and its graph is exactly the contact set. -/
theorem stationary_family_certificate
    {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {U : Set P} {V : Set E} {n : WithTop ENat}
    {F : P × E → ℝ} {ψ : P → E}
    (hF : ContDiffOn ℝ n F (U ×ˢ V)) (hψ : ContDiffOn ℝ n ψ U)
    (hψV : MapsTo ψ U V)
    (hconv : ∀ p ∈ U, StrictConvexOn ℝ V (fun z => F (p, z)))
    (hstat : ∀ p ∈ U, HasFDerivAt (fun z => F (p, z))
      (0 : E →L[ℝ] ℝ) (ψ p)) :
    ContDiffOn ℝ n (fun p => F (p, ψ p)) U ∧
      ∀ p ∈ U, ∀ z ∈ V,
        F (p, ψ p) ≤ F (p, z) ∧ (F (p, z) = F (p, ψ p) ↔ z = ψ p) := by
  constructor
  · exact hF.comp (contDiffOn_id.prodMk hψ) (fun p hp => ⟨hp, hψV hp⟩)
  · intro p hp z hz
    exact ⟨convex_isMinOn_of_hasFDerivAt_zero (hconv p hp).convexOn
      (hψV hp) (hstat p hp) hz,
      strictConvex_eq_iff_of_hasFDerivAt_zero (hconv p hp) (hψV hp) (hstat p hp) hz⟩

/-- Version of `stationary_family_certificate` using explicit positive Hessians.
This is the analytic supporting-certificate step of the local construction. -/
theorem stationary_family_certificate_of_positive_hessian
    {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {U : Set P} {V : Set E} {n : WithTop ENat}
    {F : P × E → ℝ} {ψ : P → E}
    {D : P → E → E →L[ℝ] ℝ} {H : P → E → E →L[ℝ] E →L[ℝ] ℝ}
    (hF : ContDiffOn ℝ n F (U ×ˢ V)) (hψ : ContDiffOn ℝ n ψ U)
    (hψV : MapsTo ψ U V) (hV : Convex ℝ V) (hVopen : IsOpen V)
    (hD : ∀ p ∈ U, ∀ z ∈ V, HasFDerivAt (fun z => F (p, z)) (D p z) z)
    (hH : ∀ p ∈ U, ∀ z ∈ V, HasFDerivAt (D p) (H p z) z)
    (hpos : ∀ p ∈ U, ∀ z ∈ V, ∀ v : E, v ≠ 0 → 0 < H p z v v)
    (hstat : ∀ p ∈ U, D p (ψ p) = 0) :
    ContDiffOn ℝ n (fun p => F (p, ψ p)) U ∧
      ∀ p ∈ U, ∀ z ∈ V,
        F (p, ψ p) ≤ F (p, z) ∧ (F (p, z) = F (p, ψ p) ↔ z = ψ p) := by
  apply stationary_family_certificate hF hψ hψV
  · intro p hp
    exact strictConvexOn_of_positive_hessian hV hVopen (hD p hp) (hH p hp) (hpos p hp)
  · intro p hp
    simpa [hstat p hp] using hD p hp (ψ p) (hψV hp)

end Problem356

end

end OAI

-- ---- from OAI.Analysis.CoulombTransport.HessianCoercivity ----
namespace OAI

universe uE uX

open Filter
open scoped Topology

namespace Problem356

/-- A continuous family of coercive bilinear forms remains uniformly coercive
near the base point, with half the original lower-bound constant. -/
theorem eventually_bilinear_coercive
    {X : Type uX} {E : Type uE} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : X → E →L[ℝ] E →L[ℝ] ℝ) (x₀ : X) (a : ℝ)
    (ha : 0 < a) (hcont : ContinuousAt B x₀)
    (hbase : ∀ v, a * ‖v‖ ^ 2 ≤ B x₀ v v) :
    ∀ᶠ x in 𝓝 x₀, ∀ v, (a / 2) * ‖v‖ ^ 2 ≤ B x v v := by
  have hnear : ∀ᶠ x in 𝓝 x₀, dist (B x) (B x₀) < a / 2 :=
    (Metric.tendsto_nhds.mp hcont.tendsto) (a / 2) (half_pos ha)
  filter_upwards [hnear] with x hx
  have h := bilinear_coercive_of_norm_sub_le (B x₀) (B x) a (a / 2) hbase
    (by rw [← dist_eq_norm (B x) (B x₀)]; exact hx.le)
  have haeq : a - a / 2 = a / 2 := by ring
  simpa only [haeq] using h

/-- Positive definiteness is an open condition for continuous bilinear families
on finite-dimensional real normed spaces. -/
theorem eventually_bilinear_pos
    {X : Type uX} {E : Type uE} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (B : X → E →L[ℝ] E →L[ℝ] ℝ) (x₀ : X)
    (hcont : ContinuousAt B x₀) (hpos : ∀ v, v ≠ 0 → 0 < B x₀ v v) :
    ∀ᶠ x in 𝓝 x₀, ∀ v, v ≠ 0 → 0 < B x v v := by
  obtain ⟨a, ha, hbase⟩ := exists_bilinear_coercivity_of_pos (B x₀) hpos
  filter_upwards [eventually_bilinear_coercive B x₀ a ha hcont hbase] with x hx
  intro v hv
  exact lt_of_lt_of_le (mul_pos (half_pos ha) (sq_pos_of_pos (norm_pos_iff.mpr hv))) (hx v)

end Problem356

end OAI

-- ---- from OAI.Analysis.CoulombTransport.LocalCertificate ----
namespace OAI

universe uE

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace Problem356.LocalGeometry

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Positive Hessian at the base point, together with separate local branch
invertibility, yields the full neighborhood-level supporting certificate. -/
theorem nonempty_localSupportingCharts [CompleteSpace E] [FiniteDimensional ℝ E]
    {F : E × (E × E) → ℝ} {G : E × (E × E) → E × E}
    {D : E → (E × E) → (E × E) →L[ℝ] ℝ}
    {H : E → (E × E) → (E × E) →L[ℝ] ((E × E) →L[ℝ] ℝ)}
    {p : E} {s : E × E}
    (C : LocalImplicit.AnalyticStationaryCharts G p s)
    (hF : ContDiffAt ℝ ω F (p, s))
    (hD : ∀ᶠ q in 𝓝 (p, s), HasFDerivAt (fun z => F (q.1, z)) (D q.1 q.2) q.2)
    (hH : ∀ᶠ q in 𝓝 (p, s), HasFDerivAt (D q.1) (H q.1 q.2) q.2)
    (hHcont : ContinuousAt (fun q : E × (E × E) => H q.1 q.2) (p, s))
    (hHpos : ∀ v : E × E, v ≠ 0 → 0 < H p s v v)
    (hcompatible : ∀ q : E × (E × E), G q = 0 → D q.1 q.2 = 0) :
    Nonempty (LocalSupportingCharts F G p s) := by
  let ψ : E → E × E := fun y => (C.central y, C.opposite y)
  have hψsmooth : ContDiffOn ℝ ω ψ C.central.source :=
    C.central_analytic.prodMk (C.source_eq ▸ C.opposite_analytic)
  have hψbase : ψ p = s := by simp [ψ, C.central_value, C.opposite_value]
  have hHnear := eventually_bilinear_pos (fun q : E × (E × E) => H q.1 q.2)
    (p, s) hHcont hHpos
  have hgood : ∀ᶠ q in 𝓝 (p, s), ContDiffAt ℝ ω F q ∧
      HasFDerivAt (fun z => F (q.1, z)) (D q.1 q.2) q.2 ∧
      HasFDerivAt (D q.1) (H q.1 q.2) q.2 ∧
      ∀ v : E × E, v ≠ 0 → 0 < H q.1 q.2 v v := by
    filter_upwards [hF.eventually (by simp), hD, hH, hHnear] with q h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.mp hgood
  obtain ⟨r, hr, hrB⟩ := Metric.mem_nhds_iff.mp
    (inter_mem hB (C.stateDomain_open.mem_nhds C.state_mem))
  have hψcont : ContinuousAt ψ p :=
    (hψsmooth.contDiffAt (C.central.open_source.mem_nhds C.point_mem)).continuousAt
  have hψball : ∀ᶠ y in 𝓝 p, ψ y ∈ Metric.ball s r := by
    apply hψcont.preimage_mem_nhds
    rw [hψbase]
    exact Metric.ball_mem_nhds s hr
  have hUgood : ∀ᶠ y in 𝓝 p,
      y ∈ C.central.source ∧ y ∈ A ∧ ψ y ∈ Metric.ball s r := by
    filter_upwards [C.central.open_source.mem_nhds C.point_mem, hA, hψball]
      with y h1 h2 h3
    exact ⟨h1, h2, h3⟩
  obtain ⟨t, ht, htU⟩ := Metric.mem_nhds_iff.mp hUgood
  let U := Metric.ball p t
  have hUcentral : U ⊆ C.central.source := fun _ hy => (htU hy).1
  have hUopposite : U ⊆ C.opposite.source := C.source_eq ▸ hUcentral
  let X := C.central.restrOpen U Metric.isOpen_ball
  let Z := C.opposite.restrOpen U Metric.isOpen_ball
  have hXsource : X.source = U := inter_eq_right.mpr hUcentral
  have hZsource : Z.source = U := inter_eq_right.mpr hUopposite
  have hpair : (fun y => (X y, Z y)) = ψ := rfl
  have hproperties : ∀ y ∈ U, ∀ z ∈ Metric.ball s r,
      ContDiffAt ℝ ω F (y, z) ∧
      HasFDerivAt (fun z => F (y, z)) (D y z) z ∧
      HasFDerivAt (D y) (H y z) z ∧
      ∀ v : E × E, v ≠ 0 → 0 < H y z v v := by
    intro y hy z hz
    exact hAB ⟨(htU hy).2.1, (hrB hz).1⟩
  have hψU : ContDiffOn ℝ ω ψ U := hψsmooth.mono hUcentral
  have hψUmap : MapsTo ψ U (Metric.ball s r) := fun _ hy => (htU hy).2.2
  have hstatU : ∀ y ∈ U, D y (ψ y) = 0 := by
    intro y hy
    exact hcompatible (y, ψ y) (C.stationary y (hUcentral hy))
  have hcert := stationary_family_certificate_of_positive_hessian
    (fun q hq => (hproperties q.1 hq.1 q.2 hq.2).1.contDiffWithinAt)
    hψU hψUmap (convex_ball s r) Metric.isOpen_ball
    (fun y hy z hz => (hproperties y hy z hz).2.1)
    (fun y hy z hz => (hproperties y hy z hz).2.2.1)
    (fun y hy z hz => (hproperties y hy z hz).2.2.2) hstatU
  let C' : LocalImplicit.AnalyticStationaryCharts G p s := {
    central := X
    opposite := Z
    source_eq := hXsource.trans hZsource.symm
    point_mem := by rw [hXsource]; exact Metric.mem_ball_self ht
    central_value := C.central_value
    opposite_value := C.opposite_value
    stateDomain := Metric.ball s r
    stateDomain_open := Metric.isOpen_ball
    state_mem := Metric.mem_ball_self hr
    mapsTo_state := by rw [hpair, hXsource]; exact hψUmap
    stationary := fun y hy => C.stationary y hy.1
    unique_zero := fun y hy z hz => C.unique_zero y hy.1 z (hrB hz).2
    central_analytic := C.central_analytic.mono (fun _ hy => hy.1)
    central_inverse_analytic := C.central_inverse_analytic.mono (fun _ hy => hy.1)
    opposite_analytic := C.opposite_analytic.mono (fun _ hy => hy.1)
    opposite_inverse_analytic := C.opposite_inverse_analytic.mono (fun _ hy => hy.1) }
  refine ⟨{
    charts := C'
    parameterRadius := t
    parameterRadius_pos := ht
    source_ball := hXsource
    stateRadius := r
    stateRadius_pos := hr
    state_ball := rfl
    value := fun y => F (y, ψ y)
    value_analytic := ?_
    value_eq := fun _ => rfl
    value_base := by rw [hψbase]
    supporting := ?_
    contact := ?_ }⟩
  · change ContDiffOn ℝ ω (fun y => F (y, ψ y)) X.source
    rw [hXsource]
    exact hcert.1
  · intro y hy z hz
    exact (hcert.2 y (hXsource ▸ hy) z hz).1
  · intro y hy z hz
    exact (hcert.2 y (hXsource ▸ hy) z hz).2

end Problem356.LocalGeometry

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem356 OAI.Problem356.LocalGeometry
open Set Filter
open scoped Topology ContDiff


theorem solution.{uE} : type_of% @_root_.OAI.Problem356.LocalGeometry.nonempty_localSupportingCharts.{uE} := @_root_.OAI.Problem356.LocalGeometry.nonempty_localSupportingCharts.{uE}
