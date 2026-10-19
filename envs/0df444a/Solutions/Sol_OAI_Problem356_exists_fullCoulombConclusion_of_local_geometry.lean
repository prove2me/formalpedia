-- Prove2me | solution 1 for OAI.Problem356.exists_fullCoulombConclusion_of_local_geometry
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:54:06.645481+00:00
-- url     : https://prove2.me/submissions/b23a963c-03ec-4b68-86eb-7c66d0f17fa4

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/ExistenceFromLocalGeometry.lean:L15-L98
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.exists_fullCoulombConclusion_of_local_geometry. The node keeps its source
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
import Definitions.Def_OAI_Analysis_CoulombTransport_StationaryMap
import Definitions.Def_OAI_Analysis_CoulombTransport_LocalBranchMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_SmoothPushforward
import Definitions.Def_OAI_Analysis_CoulombTransport_GluedCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_GoodTypePermutation
import Definitions.Def_OAI_Analysis_CoulombTransport_IsometryTransport
import Definitions.Def_OAI_Analysis_CoulombTransport_SmoothBranchMarginal
import Definitions.Def_OAI_Analysis_CoulombTransport_StateDual
import Theorems.Thm_OAI_Problem356_BranchSeparation_exists_ae_separated_branchCoupling
import Theorems.Thm_OAI_Problem356_SmoothBranchMarginal_exists_smoothBranchData_of_smooth_charts
import Theorems.Thm_OAI_Problem356_Transport_exists_measurable_lift_close
import Theorems.Thm_OAI_Problem356_branchCoupling_optimality_of_real_certificate
import Theorems.Thm_OAI_Problem356_finiteMongeApproximation_of_near_fst_lifts
import Theorems.Thm_OAI_Problem356_hasCoulombCounterexample_of_real_branches
import Theorems.Thm_OAI_Problem356_isProbabilityMeasure_branchCoupling

-- ---- from OAI.Analysis.CoulombTransport.BranchCoupling ----
namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Problem356

lemma measurable_branchGraph {f g h : E3 → E3}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h) :
    Measurable (branchGraph f g h) := hf.prodMk (hg.prodMk hh)

lemma map_tripleFst_branchGraph (nu : Measure E3) {f g h : E3 → E3}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h) :
    Measure.map tripleFst (Measure.map (branchGraph f g h) nu) = Measure.map f nu := by
  rw [Measure.map_map (show Measurable tripleFst from measurable_fst) (measurable_branchGraph hf hg hh)]
  rfl

lemma map_tripleSnd_branchGraph (nu : Measure E3) {f g h : E3 → E3}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h) :
    Measure.map tripleSnd (Measure.map (branchGraph f g h) nu) = Measure.map g nu := by
  rw [Measure.map_map (show Measurable tripleSnd from measurable_fst.comp measurable_snd)
    (measurable_branchGraph hf hg hh)]
  rfl

lemma map_tripleThd_branchGraph (nu : Measure E3) {f g h : E3 → E3}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h) :
    Measure.map tripleThd (Measure.map (branchGraph f g h) nu) = Measure.map h nu := by
  rw [Measure.map_map (show Measurable tripleThd from measurable_snd.comp measurable_snd)
    (measurable_branchGraph hf hg hh)]
  rfl

lemma six_smul_group (a b c d e : Measure E3) :
    (1 / 6 : ℝ≥0∞) • (a + b + c + a + d + e) =
      (1 / 3 : ℝ≥0∞) • a + (1 / 6 : ℝ≥0∞) • (b + c + d + e) := by
  have h : (1 / 3 : ℝ≥0∞) = 1 / 6 + 1 / 6 := by
    simp only [one_div]
    change ((3 : NNReal) : ℝ≥0∞)⁻¹ = ((6 : NNReal) : ℝ≥0∞)⁻¹ +
      ((6 : NNReal) : ℝ≥0∞)⁻¹
    rw [← ENNReal.coe_inv (by norm_num : (3 : NNReal) ≠ 0),
      ← ENNReal.coe_inv (by norm_num : (6 : NNReal) ≠ 0), ← ENNReal.coe_add]
    norm_num
  rw [h, add_smul]
  simp only [smul_add]
  ac_rfl

lemma map_tripleFst_branchCoupling (nu : Measure E3) {H1 H2 H3 H4 : E3 → E3}
    (h1 : Measurable H1) (h2 : Measurable H2) (h3 : Measurable H3)
    (h4 : Measurable H4) :
    Measure.map tripleFst (branchCoupling nu H1 H2 H3 H4) =
      branchMarginal nu H1 H2 H3 H4 := by
  have hp : Measurable tripleFst := measurable_fst
  simp only [branchCoupling, Measure.map_smul _ _ tripleFst, Measure.map_add _ _ hp,
    map_tripleFst_branchGraph nu measurable_id h1 h2,
    map_tripleFst_branchGraph nu h1 h2 measurable_id,
    map_tripleFst_branchGraph nu h2 measurable_id h1,
    map_tripleFst_branchGraph nu measurable_id h3 h4,
    map_tripleFst_branchGraph nu h3 h4 measurable_id,
    map_tripleFst_branchGraph nu h4 measurable_id h3, Measure.map_id]
  exact six_smul_group _ _ _ _ _

lemma map_tripleSnd_branchCoupling (nu : Measure E3) {H1 H2 H3 H4 : E3 → E3}
    (h1 : Measurable H1) (h2 : Measurable H2) (h3 : Measurable H3)
    (h4 : Measurable H4) :
    Measure.map tripleSnd (branchCoupling nu H1 H2 H3 H4) =
      branchMarginal nu H1 H2 H3 H4 := by
  have hp : Measurable tripleSnd := measurable_fst.comp measurable_snd
  simp only [branchCoupling, Measure.map_smul _ _ tripleSnd, Measure.map_add _ _ hp,
    map_tripleSnd_branchGraph nu measurable_id h1 h2,
    map_tripleSnd_branchGraph nu h1 h2 measurable_id,
    map_tripleSnd_branchGraph nu h2 measurable_id h1,
    map_tripleSnd_branchGraph nu measurable_id h3 h4,
    map_tripleSnd_branchGraph nu h3 h4 measurable_id,
    map_tripleSnd_branchGraph nu h4 measurable_id h3, Measure.map_id]
  unfold branchMarginal
  rw [← six_smul_group]
  congr 1
  ac_rfl

lemma map_tripleThd_branchCoupling (nu : Measure E3) {H1 H2 H3 H4 : E3 → E3}
    (h1 : Measurable H1) (h2 : Measurable H2) (h3 : Measurable H3)
    (h4 : Measurable H4) :
    Measure.map tripleThd (branchCoupling nu H1 H2 H3 H4) =
      branchMarginal nu H1 H2 H3 H4 := by
  have hp : Measurable tripleThd := measurable_snd.comp measurable_snd
  simp only [branchCoupling, Measure.map_smul _ _ tripleThd, Measure.map_add _ _ hp,
    map_tripleThd_branchGraph nu measurable_id h1 h2,
    map_tripleThd_branchGraph nu h1 h2 measurable_id,
    map_tripleThd_branchGraph nu h2 measurable_id h1,
    map_tripleThd_branchGraph nu measurable_id h3 h4,
    map_tripleThd_branchGraph nu h3 h4 measurable_id,
    map_tripleThd_branchGraph nu h4 measurable_id h3, Measure.map_id]
  unfold branchMarginal
  rw [← six_smul_group]
  congr 1
  ac_rfl

/-- The explicit two-branch mixture is an admissible coupling of its five-component marginal. -/
theorem isThreeCoupling_branchCoupling (nu : Measure E3) [IsProbabilityMeasure nu]
    {H1 H2 H3 H4 : E3 → E3}
    (h1 : Measurable H1) (h2 : Measurable H2) (h3 : Measurable H3)
    (h4 : Measurable H4) :
    IsThreeCoupling (branchMarginal nu H1 H2 H3 H4) (branchCoupling nu H1 H2 H3 H4) :=
  ⟨isProbabilityMeasure_branchCoupling nu h1 h2 h3 h4,
    map_tripleFst_branchCoupling nu h1 h2 h3 h4,
    map_tripleSnd_branchCoupling nu h1 h2 h3 h4,
    map_tripleThd_branchCoupling nu h1 h2 h3 h4⟩

end Problem356

end

end OAI

-- ---- from OAI.Analysis.CoulombTransport.BranchSeparation ----
namespace OAI

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Problem356.BranchSeparation

/-- A compact subcomponent retains disjointness of the larger local domains. -/
lemma disjoint_components_mono {K B : Set E3} (hKB : K ⊆ B)
    {H : Fin 4 → E3 → E3}
    (hB : Pairwise (fun i j => Disjoint (components B H i) (components B H j))) :
    Pairwise (fun i j => Disjoint (components K H i) (components K H j)) := by
  have hsub : ∀ i, components K H i ⊆ components B H i := by
    intro i
    exact Fin.cases hKB (fun j => image_mono hKB) i
  intro i j hij
  exact (hB hij).mono (hsub i) (hsub j)

end Problem356.BranchSeparation

end

end OAI

-- ---- from OAI.Analysis.CoulombTransport.GraphBridge ----
namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Problem356

lemma measurable_tripleFst : Measurable tripleFst := measurable_fst
lemma measurable_tripleSnd : Measurable tripleSnd := measurable_fst.comp measurable_snd
lemma measurable_tripleThd : Measurable tripleThd := measurable_snd.comp measurable_snd

lemma measurable_invDistance : Measurable (fun p : E3 × E3 => invDistance p.1 p.2) := by
  unfold invDistance
  exact ((measurable_fst.sub measurable_snd).norm.ennreal_ofReal).inv

lemma measurable_coulombCost : Measurable coulombCost := by
  unfold coulombCost
  exact ((measurable_invDistance.comp (measurable_tripleFst.prodMk measurable_tripleSnd)).add
    (measurable_invDistance.comp (measurable_tripleFst.prodMk measurable_tripleThd))).add
    (measurable_invDistance.comp (measurable_tripleSnd.prodMk measurable_tripleThd))

lemma measurable_graphMap {T2 T3 : E3 → E3} (h2 : Measurable T2) (h3 : Measurable T3) :
    Measurable (graphMap T2 T3) := measurable_id.prodMk (h2.prodMk h3)

lemma graphMeasure_isThreeCoupling (mu : Measure E3) [IsProbabilityMeasure mu]
    {T2 T3 : E3 → E3} (h2 : Preserves mu T2) (h3 : Preserves mu T3) :
    IsThreeCoupling mu (graphMeasure mu T2 T3) := by
  have hm := measurable_graphMap h2.1 h3.1
  refine ⟨(Measure.isProbabilityMeasure_map_iff hm.aemeasurable).mpr inferInstance,
    ?_, ?_, ?_⟩
  · rw [graphMeasure, Measure.map_map measurable_tripleFst hm]
    change Measure.map id mu = mu
    exact Measure.map_id
  · rw [graphMeasure, Measure.map_map measurable_tripleSnd hm]
    exact h2.2
  · rw [graphMeasure, Measure.map_map measurable_tripleThd hm]
    exact h3.2

lemma lintegral_graphMeasure (mu : Measure E3) {T2 T3 : E3 → E3}
    (h2 : Measurable T2) (h3 : Measurable T3) :
    (∫⁻ t, coulombCost t ∂graphMeasure mu T2 T3) = graphCost mu T2 T3 := by
  exact lintegral_map measurable_coulombCost (measurable_graphMap h2 h3)

lemma kantorovichValue_le_graphCost (mu : Measure E3) [IsProbabilityMeasure mu]
    {T2 T3 : E3 → E3} (h2 : Preserves mu T2) (h3 : Preserves mu T3) :
    kantorovichValue mu ≤ graphCost mu T2 T3 := by
  rw [← lintegral_graphMeasure mu h2.1 h3.1]
  exact iInf₂_le (graphMeasure mu T2 T3) (graphMeasure_isThreeCoupling mu h2 h3)

lemma kantorovichValue_le_mongeValue (mu : Measure E3) [IsProbabilityMeasure mu] :
    kantorovichValue mu ≤ mongeValue mu := by
  unfold mongeValue
  exact le_iInf fun T2 => le_iInf fun T3 => le_iInf fun h2 => le_iInf fun h3 =>
    kantorovichValue_le_graphCost mu h2 h3

end Problem356

end

end OAI

-- ---- from OAI.Analysis.CoulombTransport.DensityMeasure ----
namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356

/-- A density measure gives no mass to the complement of its topological support. -/
theorem densityMeasure_tsupport_compl (rho : E3 → ℝ) :
    densityMeasure rho (tsupport rho)ᶜ = 0 := by
  rw [densityMeasure, withDensity_apply _ (isClosed_tsupport rho).measurableSet.compl]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_mem (isClosed_tsupport rho).measurableSet.compl] with x hx
  simp only [Pi.zero_apply]
  rw [image_eq_zero_of_notMem_tsupport hx, ENNReal.ofReal_zero]

/-- Compact support of the density provides an explicit compact set of full measure. -/
theorem densityMeasure_exists_compact_conull {rho : E3 → ℝ}
    (hrho : HasCompactSupport rho) :
    ∃ K : Set E3, IsCompact K ∧ densityMeasure rho Kᶜ = 0 :=
  ⟨tsupport rho, hrho, densityMeasure_tsupport_compl rho⟩

end Problem356

end

end OAI

-- ---- from OAI.Analysis.CoulombTransport.EqualInfima ----
namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Problem356

/-- Every feasible Monge pair bounds its defining infimum from above. -/
theorem mongeValue_le_graphCost (mu : Measure E3) {T2 T3 : E3 → E3}
    (h2 : Preserves mu T2) (h3 : Preserves mu T3) :
    mongeValue mu ≤ graphCost mu T2 T3 := by
  exact iInf_le_of_le T2 (iInf_le_of_le T3 (iInf_le_of_le h2 (iInf_le _ h3)))

/-- Arbitrarily accurate finite preserving-map approximations imply equality of values. -/
theorem FiniteMongeApproximation.equal_infima {mu : Measure E3}
    [IsProbabilityMeasure mu] (h : FiniteMongeApproximation mu) :
    mongeValue mu = kantorovichValue mu := by
  apply le_antisymm _ (kantorovichValue_le_mongeValue mu)
  apply ENNReal.le_of_forall_pos_le_add
  intro epsilon hepsilon _
  obtain ⟨T2, T3, h2, h3, _, hcost⟩ := h epsilon hepsilon
  exact (mongeValue_le_graphCost mu h2 h3).trans (by simpa using hcost)

/-- The full target conclusion follows once the counterexample and finite approximation
have been constructed for the same density. -/
theorem HasCoulombCounterexample.fullConclusion {rho : E3 → ℝ}
    (h : HasCoulombCounterexample rho)
    (happrox : FiniteMongeApproximation (densityMeasure rho)) :
    HasFullCoulombConclusion rho := by
  have : IsProbabilityMeasure (densityMeasure rho) := h.2.1
  exact ⟨h, happrox.equal_infima, happrox⟩

end Problem356

end

end OAI

-- ---- from OAI.Analysis.CoulombTransport.CompactLiftApproximation ----
namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Problem356

/-- A compactly supported atomless marginal and a uniformly separated optimal
coupling admit finite-cost deterministic approximations. -/
theorem finiteMongeApproximation_of_compact_separated_optimizer
    {mu : Measure E3} [IsProbabilityMeasure mu] [NullSingletonClass mu]
    {pi : Measure Triple} (hpi : IsThreeCoupling mu pi)
    (hoptimal : (∫⁻ t, coulombCost t ∂pi) = kantorovichValue mu)
    {K : Set E3} (hK : IsCompact K) (hfull : mu Kᶜ = 0)
    {eta : ℝ} (heta : 0 < eta)
    (hseparated : ∀ᵐ t ∂pi, CoulombEstimates.Separated eta t) :
    FiniteMongeApproximation mu := by
  have : IsProbabilityMeasure pi := hpi.1
  apply finiteMongeApproximation_of_near_fst_lifts hpi hoptimal heta hseparated
  intro delta hdelta
  obtain ⟨Q, hQ, hmap, hclose⟩ := Transport.exists_measurable_lift_close
    mu pi tripleFst measurable_tripleFst hpi.2.1 hK hfull hdelta
  exact ⟨Q, hQ, hmap, hclose.mono fun _ hx => hx.le⟩

/-- A Coulomb counterexample with a separated optimal plan and compactly supported
density has equal Monge and Kantorovich infima and finite-cost Monge approximations. -/
theorem HasCoulombCounterexample.hasFull_of_separated_optimizer
    {rho : E3 → ℝ} (hcounter : HasCoulombCounterexample rho)
    {pi : Measure Triple} (hpi : IsThreeCoupling (densityMeasure rho) pi)
    (hoptimal : (∫⁻ t, coulombCost t ∂pi) = kantorovichValue (densityMeasure rho))
    {eta : ℝ} (heta : 0 < eta)
    (hseparated : ∀ᵐ t ∂pi, CoulombEstimates.Separated eta t) :
    HasFullCoulombConclusion rho := by
  have : IsProbabilityMeasure (densityMeasure rho) := hcounter.2.1
  obtain ⟨K, hK, hfull⟩ := densityMeasure_exists_compact_conull hcounter.1.2.2.1
  have happ := finiteMongeApproximation_of_compact_separated_optimizer
    hpi hoptimal hK hfull heta hseparated
  exact hcounter.fullConclusion happ

end Problem356

end

end OAI

-- ---- from OAI.Analysis.CoulombTransport.ExistenceFromLocalGeometry ----
namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356

theorem exists_fullCoulombConclusion_of_local_geometry
    (c : E3) {r : ℝ} (hr : 0 < r)
    (e : Fin 4 → OpenPartialHomeomorph E3 E3)
    (hsource : ∀ i, Metric.ball c r ⊆ (e i).source)
    (hdisj : Pairwise (fun i j => Disjoint
      (SmoothBranchMarginal.componentRegion (Metric.ball c r) e i)
      (SmoothBranchMarginal.componentRegion (Metric.ball c r) e j)))
    (he : ∀ i, ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) (e i) (e i).source)
    (he' : ∀ i, ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) (e i).symm (e i).target)
    {U : Set E3} (hU : MeasurableSet U)
    (hBU : Metric.ball c r ⊆ U) (heU : ∀ i, e i '' Metric.ball c r ⊆ U)
    {u : E3 → ℝ} (hu : Measurable u) {M : ℝ} (hM : 0 ≤ M)
    (hubound : ∀ x ∈ U, -M ≤ u x ∧ u x ≤ M)
    (hbound : ∀ t, tripleFst t ∈ U → tripleSnd t ∈ U → tripleThd t ∈ U →
      ENNReal.ofReal (u (tripleFst t) + u (tripleSnd t) + u (tripleThd t)) ≤
        coulombCost t)
    (hcontact01 : ∀ x ∈ Metric.ball c r,
      ENNReal.ofReal (u x + u (e 0 x) + u (e 1 x)) = coulombCost (x, (e 0 x, e 1 x)))
    (hcontact23 : ∀ x ∈ Metric.ball c r,
      ENNReal.ofReal (u x + u (e 2 x) + u (e 3 x)) = coulombCost (x, (e 2 x, e 3 x)))
    (hselect : ∀ x y z : E3, x ∈ Metric.ball c r → y ∈ U → z ∈ U →
      ENNReal.ofReal (u x + u y + u z) = coulombCost (x, (y, z)) →
      ∃ i, y = e i x) :
    ∃ rho : E3 → ℝ, HasFullCoulombConclusion rho := by
  obtain ⟨d, hd⟩ := SmoothBranchMarginal.exists_smoothBranchData_of_smooth_charts
    c hr e hsource hdisj he he'
  have : IsProbabilityMeasure d.nu := d.probability
  have hfull : ∀ᵐ x ∂d.nu, x ∈ Metric.ball c r :=
    d.core_full.mono (fun _ hx => d.core_subset hx)
  have hdensity : densityMeasure d.rho =
      branchMarginal d.nu (d.branch 0) (d.branch 1) (d.branch 2) (d.branch 3) := by
    simpa [branchMarginal, Fin.sum_univ_succ, smul_add, add_assoc] using d.density_eq
  have hHU : ∀ i, d.branch i '' Metric.ball c r ⊆ U := by
    rintro i _ ⟨x, hx, rfl⟩
    rw [hd i x hx]
    exact heU i ⟨x, hx, rfl⟩
  have hCentral : ∀ i, Disjoint (Metric.ball c r) (d.branch i '' Metric.ball c r) := by
    intro i
    exact d.component_disjoint (show (none : Option (Fin 4)) ≠ some i by simp)
  have hPair : Pairwise fun i j =>
      Disjoint (d.branch i '' Metric.ball c r) (d.branch j '' Metric.ball c r) := by
    intro i j hij
    exact d.component_disjoint (show some i ≠ some j by simpa using hij)
  have hc01 : ∀ᵐ x ∂d.nu,
      ENNReal.ofReal (u x + u (d.branch 0 x) + u (d.branch 1 x)) =
        coulombCost (x, (d.branch 0 x, d.branch 1 x)) := by
    filter_upwards [hfull] with x hx
    simpa only [hd 0 x hx, hd 1 x hx] using hcontact01 x hx
  have hc23 : ∀ᵐ x ∂d.nu,
      ENNReal.ofReal (u x + u (d.branch 2 x) + u (d.branch 3 x)) =
        coulombCost (x, (d.branch 2 x, d.branch 3 x)) := by
    filter_upwards [hfull] with x hx
    simpa only [hd 2 x hx, hd 3 x hx] using hcontact23 x hx
  have hcounter : HasCoulombCounterexample d.rho := by
    apply hasCoulombCounterexample_of_real_branches d.rho d.density_smooth d.nu
      d.branch d.branch_measurable hdensity d.measurable_central hU hfull hBU hHU
      d.branch_injective d.branch_image_measurable hCentral hPair
      hu hM hubound hbound hc01 hc23
    intro x y z hx hy hz hc
    obtain ⟨i, hi⟩ := hselect x y z hx hy hz hc
    exact ⟨i, hi.trans (hd i x hx).symm⟩
  have hoptimal := branchCoupling_optimality_of_real_certificate d.nu d.branch
    d.branch_measurable hU hfull hBU hHU hu hM hubound hbound hc01 hc23
  have hdisjoint : Pairwise (fun i j =>
      Disjoint (BranchSeparation.components d.compactCore d.branch i)
        (BranchSeparation.components d.compactCore d.branch j)) := by
    apply BranchSeparation.disjoint_components_mono d.core_subset
    intro i j hij
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact (hij rfl).elim
      | succ j => exact hCentral j
    | succ i =>
      induction j using Fin.cases with
      | zero => exact (hCentral i).symm
      | succ j => exact hPair (by simpa using hij)
  obtain ⟨eta, heta, hsep⟩ := BranchSeparation.exists_ae_separated_branchCoupling
    d.core_compact d.core_full d.branch_measurable d.branch_continuous hdisjoint
  refine ⟨d.rho, hcounter.hasFull_of_separated_optimizer ?_ ?_ heta hsep⟩
  · rw [hdensity]
    exact isThreeCoupling_branchCoupling d.nu (d.branch_measurable 0)
      (d.branch_measurable 1) (d.branch_measurable 2) (d.branch_measurable 3)
  · simpa only [hdensity] using hoptimal.1

end Problem356

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem356
open MeasureTheory
open scoped ENNReal


theorem solution : type_of% @_root_.OAI.Problem356.exists_fullCoulombConclusion_of_local_geometry := @_root_.OAI.Problem356.exists_fullCoulombConclusion_of_local_geometry
