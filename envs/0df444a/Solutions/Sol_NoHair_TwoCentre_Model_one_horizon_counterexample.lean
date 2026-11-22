-- Prove2me | solution 1 for NoHair.TwoCentre.Model.one_horizon_counterexample
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T21:52:00.676057+00:00
-- url     : https://prove2.me/submissions/2e922220-e0f5-4ecb-b80b-e404f4bea0ab
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_NoHair_TwoCentre_Model_stationary_geometry
import Theorems.Thm_NoHair_TwoCentre_Model_electrovac_in_advanced_atlas
import Theorems.Thm_NoHair_TwoCentre_Model_chronological_access
import Theorems.Thm_NoHair_TwoCentre_Model_global_hyperbolicity
import Theorems.Thm_NoHair_TwoCentre_isotropic_electrovac_and_decay
import Theorems.Thm_NoHair_TwoCentre_Cartesian_exterior_and_frontier
import Theorems.Thm_NoHair_TwoCentre_not_israel_conclusion

open NoHair NoHair.TwoCentre NoHair.TwoCentre.Cartesian NoHair.TwoCentre.Model Set Filter Topology
open scoped ContDiff Manifold

private theorem spatial_cont : Continuous spatial := by
  have h : ContDiff ℝ ∞ spatial := contDiff_euclidean.2 (fun i => contDiff_piLp_apply (p := 2) (i := i.succ))
  exact h.continuous

private theorem outer_open : IsOpen Model.outer := by
  have h : IsOpen outerRegion := (isOpen_lt continuous_const spatial_cont.norm).inter
    (isOpen_ne_fun spatial_cont continuous_const)
  exact h.preimage continuous_subtype_val

private theorem outer_subset : outerRegion ⊆ spacetime := by
  intro z hz
  exact ⟨lt_trans (by norm_num) hz.1, hz.2⟩

private theorem model_chart_val {y : E4} (hy : y ∈ exterior) :
    (Model.chart y : E4) = toAdvanced y := by
  obtain ⟨_, hmap, _⟩ := Cartesian.exterior_and_frontier.2.1
  simp [Model.chart, outer_subset (hmap hy)]

private theorem model_chart_diffeo : IsDiffeoOnto Model.chart exterior Model.outer := by
  obtain ⟨χ, hf, hb, hl, hr, hfs, hbs⟩ := Cartesian.exterior_and_frontier.2.1
  have hm : MapsTo Model.chart exterior Model.outer := by
    intro y hy
    change (Model.chart y : E4) ∈ outerRegion
    rw [model_chart_val hy]
    exact hf hy
  refine ⟨χ ∘ Subtype.val, hm, (fun _ hy => hb hy), ?_, ?_, ?_, ?_⟩
  · intro y hy
    change χ (Model.chart y : E4) = y
    rw [model_chart_val hy, hl hy]
  · intro z hz
    apply Subtype.ext
    exact (model_chart_val (hb hz)).trans (hr hz)
  · intro y hy
    apply (ContMDiffWithinAt.subtypeVal_comp_iff manifold Model.chart exterior y).mp
    exact hfs.congr (fun _ hz => model_chart_val hz) y hy
  · exact hbs.comp (contMDiff_subtype_val.contMDiffOn) (fun _ hz => hz)

private theorem restrict_chart {S : Set E4} (hS : IsOpen S) (hsub : S ⊆ exterior) :
    IsDiffeoOnto Model.chart S (Model.chart '' S) ∧ IsOpen (Model.chart '' S) := by
  obtain ⟨χ, hf, hb, hl, hr, hfs, hbs⟩ := model_chart_diffeo
  have him : Model.chart '' S = Model.outer ∩ χ ⁻¹' S := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨hf (hsub hy), ?_⟩
      change χ (Model.chart y) ∈ S
      rwa [hl (hsub hy)]
    · rintro ⟨hz, hχ⟩
      exact ⟨χ z, hχ, hr hz⟩
  have hD : Model.chart '' S ⊆ Model.outer := him ▸ inter_subset_left
  refine ⟨⟨χ, fun y hy => mem_image_of_mem _ hy, ?_, hl.mono hsub, hr.mono hD,
    hfs.mono hsub, hbs.mono hD⟩, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    rw [hl (hsub hy)]
    exact hy
  · rw [him]
    exact hbs.continuousOn.isOpen_inter_preimage outer_open hS

private theorem end_equivariant (s : ℝ) (y : E4) (hy : y ∈ exteriorRegion 2) :
    Model.chart (y + s • coordBasis 0) = flow s (Model.chart y) := by
  have hy' := (isotropic_electrovac_and_decay.2 y hy).1
  have ht : spatial (y + s • coordBasis 0) = spatial y := by
    ext i
    simp [spatial, coordBasis]
  have hs : spatialRadius (y + s • coordBasis 0) = spatialRadius y := by
    simp (config := {decide := true}) [spatialRadius, coordBasis]
  have hy₂ := (isotropic_electrovac_and_decay.2 (y + s • coordBasis 0) (by rw [hs]; exact hy)).1
  apply Subtype.ext
  rw [model_chart_val hy₂]
  change toAdvanced _ = coordinates ((Model.chart y : E4) 0 + s) (spatial (Model.chart y))
  rw [model_chart_val hy']
  simp only [toAdvanced, ht, Model.spatial_coordinates]
  congr 1
  change (y + s • coordBasis 0) 0 + _ = (y 0 + _) + s
  simp [coordBasis]
  ring

private theorem model_end
    (hmatch : ∀ y ∈ exterior, pullbackCoeffs metric Model.chart y = isotropicMetric y ∧
      pullbackCoeffs faraday Model.chart y = TwoCentre.field y) :
    ∃ E : AsymptoticallyFlatEnd metric faraday flow, E.region = Model.chart '' exteriorRegion 2 := by
  have hop : IsOpen (exteriorRegion 2) := isOpen_lt continuous_const (by unfold spatialRadius; fun_prop)
  have hsub : exteriorRegion 2 ⊆ exterior := fun y hy => (isotropic_electrovac_and_decay.2 y hy).1
  have hs (c : ℝ) : Continuous (squaredDistance c) := by unfold squaredDistance; fun_prop
  have heo : IsOpen exterior := (isOpen_lt continuous_const (hs (-1))).inter
    (isOpen_lt continuous_const (hs 1))
  have hd (y : E4) (hy : y ∈ exteriorRegion 2) (i j k : Fin 4) :
      coordPartial (fun z => pullbackCoeffs metric Model.chart z i j) k y =
      coordPartial (fun z => isotropicMetric z i j) k y := by
    have eqv : (fun z => pullbackCoeffs metric Model.chart z i j) =ᶠ[𝓝 y]
        (fun z => isotropicMetric z i j) := by
      filter_upwards [heo.mem_nhds (hsub hy)] with z hz using congrFun (congrFun (hmatch z hz).1 i) j
    unfold coordPartial
    rw [eqv.fderiv_eq]
  obtain ⟨hchart, hopen⟩ := restrict_chart hop hsub
  let E : AsymptoticallyFlatEnd metric faraday flow := {
    R := 2, ψ := Model.chart, C := 64, R_pos := by norm_num
    diffeo := hchart, isOpen_image := hopen, equivariant := end_equivariant
    metric_decay := by
      intro y hy i j
      rw [(hmatch y (hsub hy)).1]
      exact ((isotropic_electrovac_and_decay.2 y hy).2 i j 0).1
    metric_deriv_decay := by
      intro y hy i j k
      rw [hd y hy i j k]
      exact ((isotropic_electrovac_and_decay.2 y hy).2 i j k).2.1
    field_decay := by
      intro y hy i j
      rw [(hmatch y (hsub hy)).2]
      exact ((isotropic_electrovac_and_decay.2 y hy).2 i j 0).2.2 }
  exact ⟨E, rfl⟩

theorem solution :
    ∃ E : AsymptoticallyFlatEnd metric faraday flow,
      IsStationaryBlackHole metric faraday orientation flow E ∧
      IsStaticOn metric flow (domainOfOuterCommunications metric orientation E.region) ∧
      ¬ ∃ m e : ℝ, IsKerrNewmanBlackHoleParams m 0 e ∧
        IsKerrNewmanDOC metric faraday (domainOfOuterCommunications metric orientation E.region) m 0 e := by
  obtain ⟨hg, hsm, hsf, htwo, htime, hflow, hstatic, hmatch⟩ := Model.stationary_geometry
  obtain ⟨E, hE⟩ := model_end hmatch
  obtain ⟨hp, hf⟩ := Model.chronological_access
  have hp' : chronoPastSet metric orientation E.region = Model.outer := hE ▸ hp
  have hd : domainOfOuterCommunications metric orientation E.region = Model.outer := by
    rw [domainOfOuterCommunications, hp', hE]
    exact inter_eq_right.mpr hf
  have hfront : frontier Model.outer = {z : manifold | (z : E4) ∈ Cartesian.horizon} :=
    Cartesian.exterior_and_frontier.2.2.1
  have hc : IsConnected (frontier Model.outer) := hfront ▸ Cartesian.exterior_and_frontier.2.2.2
  have hblack : (blackHoleRegion metric orientation E.region).Nonempty := by
    rw [blackHoleRegion, hp']
    obtain ⟨z, hz⟩ := hc.nonempty
    refine ⟨z, ?_⟩
    rw [hfront] at hz
    have hz' : ‖spatial (z : E4)‖ = 1 := hz
    intro hzin
    exact (lt_irrefl (1 : ℝ)) (hz' ▸ hzin.1)
  refine ⟨E, ⟨hg, hsm, hsf, htwo, htime, Model.electrovac_in_advanced_atlas
    isotropic_electrovac_and_decay.1, hflow, hd ▸ Model.global_hyperbolicity, hblack, ?_⟩,
    hd ▸ hstatic, ?_⟩
  · simpa [futureEventHorizon, hp'] using hc
  · rw [hd]
    exact not_israel_conclusion metric faraday Model.outer outer_open Model.chart model_chart_diffeo
      (fun y hy => (hmatch y hy).2)
