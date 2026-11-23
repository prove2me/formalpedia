-- Prove2me | solution 3 for NoHair.israel_static_electrovac
-- status  : ACCEPTED   (disprove)
-- author  : @Igor Valuev
-- created : 2026-11-23T00:01:03.113392+00:00
-- url     : https://prove2.me/submissions/c265fe7d-5320-4de6-b8fb-160e352220d4

import Definitions.Def_Atlas_EinsteinMaxwell_ChartSolution
import Definitions.Def_NoHair_TwoCentreStandardEnd
import Definitions.Def_NoHair_TwoCentreCompactCausalIntervals
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_DeterminantDerivative
import Definitions.Def_NoHair_KerrNewmanEinstein_Atoms
import Definitions.Def_NoHair_KerrNewmanEinstein_MaxwellF
set_option linter.all false

/-! Full two-centre witness and coordinate covariance proofs. Public source submissions:
https://prove2.me/submissions/64cfed7a-12e5-4c5a-98c3-5d6cdf6be89c
https://prove2.me/submissions/54ab245e-b5e9-4c0d-8d7d-23f2257d6ca4
https://prove2.me/submissions/5148d962-38d9-41a3-af23-e3de1752b678
https://prove2.me/submissions/1a38b27f-8565-4a06-948a-cf826a98147b
https://prove2.me/submissions/c77be6c1-2e96-4972-ad35-8ec42732b151
https://prove2.me/submissions/ce54483a-45d8-4b83-9fad-1de2b323f24e
https://prove2.me/submissions/957172ab-b5d6-4007-aa4f-32e6917990e9
https://prove2.me/submissions/54a511d5-ae1c-479b-af34-66d077a4e96e
https://prove2.me/submissions/05ab9ff5-0dd7-4769-9e61-5893c59a0366
https://prove2.me/submissions/7b48c831-9efc-4088-b1e9-ca64179c383a
https://prove2.me/submissions/923ea4ab-4ea3-4a86-b55c-e941aa21668a
https://prove2.me/submissions/edd46219-5d5a-4adc-a78d-9deb92001a1f
https://prove2.me/submissions/cfe34a12-badd-4814-8461-38dc29911347
https://prove2.me/submissions/21d91e41-8866-461c-ae85-da4077851a0e
https://prove2.me/submissions/c32b798d-88a8-4094-895a-8a53b0262a06
https://prove2.me/submissions/12a6cbf1-905e-47f9-a5b1-a58827711ae7
https://prove2.me/submissions/78a8402b-193c-41c4-8a9c-e68130d6892c
https://prove2.me/submissions/634b4323-0fb3-43e8-968c-1012b4eb91c7
https://prove2.me/submissions/0602f095-5c6f-4ccd-ba70-5b183523cf10
https://prove2.me/submissions/e23b32ec-82f0-4bf9-8476-f725ef966eb8
-/

namespace ElectrovacProof001

open Set Filter Topology
open scoped ContDiff

namespace NoHair.TwoCentre.Advanced
open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Advanced

noncomputable section

export _root_.TwoCentreEndCollar.NoHair.TwoCentre.Advanced (collar_positive)

theorem gap_factor {p : ℝ × ℝ} (harg : 0 < 4 + p.1 ^ 2 - 4 * p.1 * p.2) :
    H p - H₀ p = p.1 ^ 2 * gapCoeff p := by
  have hd : 0 < distanceToOther p := Real.sqrt_pos.2 harg
  have hd2 : distanceToOther p ^ 2 = 4 + p.1 ^ 2 - 4 * p.1 * p.2 :=
    Real.sq_sqrt harg.le
  unfold H H₀ gapCoeff
  field_simp [hd.ne', show 2 + distanceToOther p ≠ 0 by linarith]
  linear_combination -p.1 * hd2

theorem coefficient_analytic {p : ℝ × ℝ}
    (harg : 0 < 4 + p.1 ^ 2 - 4 * p.1 * p.2) (hH : 0 < H p) :
    ∀ f ∈ [gvv, gvr, grr, angularScale, potentialV, potentialR], AnalyticAt ℝ f p := by
  have hd : 0 < distanceToOther p := Real.sqrt_pos.2 harg
  have hd' : 0 < 2 + distanceToOther p := by linarith
  have ds : ContDiffAt ℝ ω distanceToOther p := by
    unfold distanceToOther
    exact (show ContDiffAt ℝ ω (fun q : ℝ × ℝ => 4 + q.1 ^ 2 - 4 * q.1 * q.2) p
      by fun_prop).sqrt harg.ne'
  have hs : ContDiffAt ℝ ω H p := by unfold H; fun_prop (disch := positivity)
  have h0s : ContDiffAt ℝ ω H₀ p := by unfold H₀; fun_prop
  have cs : ContDiffAt ℝ ω gapCoeff p := by unfold gapCoeff; fun_prop (disch := positivity)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl <;> apply ContDiffAt.analyticAt <;>
    first | unfold gvv | unfold gvr | unfold grr | unfold angularScale | unfold potentialV |
      unfold potentialR
  all_goals fun_prop (disch := positivity)

theorem determinant {p : ℝ × ℝ} (hH : H p ≠ 0)
    (hgap : H p - H₀ p = p.1 ^ 2 * gapCoeff p) :
    gvv p * grr p - gvr p ^ 2 = -1 := by
  unfold gvv grr gvr
  field_simp [hH]
  linear_combination (H p + H₀ p) * (H p ^ 2 + H₀ p ^ 2) * hgap

theorem match_exterior {p : ℝ × ℝ} (hr : p.1 ≠ 0) (hH : H p ≠ 0)
    (hgap : H p - H₀ p = p.1 ^ 2 * gapCoeff p) :
    grr p = (H p ^ 4 - H₀ p ^ 4) / (p.1 ^ 2 * H p ^ 2) ∧
      potentialR p = -(H₀ p ^ 2 / (p.1 * H p)) + H₀ p / p.1 := by
  constructor
  · unfold grr
    field_simp [hr, hH]
    linear_combination -(H p + H₀ p) * (H p ^ 2 + H₀ p ^ 2) * hgap
  · unfold potentialR
    field_simp [hr, hH]
    linear_combination -H₀ p * hgap

theorem horizon_values (c : ℝ) :
    gvv (0, c) = 0 ∧ gvr (0, c) = 1 ∧ grr (0, c) = c ∧ angularScale (0, c) = 1 := by
  norm_num [gvv, gvr, grr, angularScale, H, H₀, gapCoeff, distanceToOther]
  ring

theorem future_radial_negative {b v w a : ℝ} (ha : 0 ≤ a)
    (htime : 2 * v * w + b * w ^ 2 + a < 0)
    (hfuture : -v + (1 - b) * w / 2 < 0) : w < 0 := by
  by_contra! hn
  nlinarith [mul_nonpos_of_nonpos_of_nonneg hfuture.le hn, sq_nonneg w]

/-- A continuous radial coordinate cannot go from nonpositive to positive if all
its zeroes on the interval have strictly inward velocity. -/
theorem no_outward_crossing {r : ℝ → ℝ} (hc : Continuous r)
    (hzero : ∀ t ∈ Icc (0 : ℝ) 1, r t = 0 → ∃ w < 0, HasDerivAt r w t)
    (hin : r 0 ≤ 0) : r 1 ≤ 0 := by
  by_contra! hout
  let Z := Icc (0 : ℝ) 1 ∩ r ⁻¹' {0}
  have hcompact : IsCompact Z := isCompact_Icc.inter_right (isClosed_singleton.preimage hc)
  obtain ⟨z₀, hz₀, hz₀r⟩ := intermediate_value_Icc zero_le_one hc.continuousOn
    (show 0 ∈ Icc (r 0) (r 1) from ⟨hin, hout.le⟩)
  obtain ⟨z, hz, hmax⟩ := hcompact.exists_isGreatest ⟨z₀, hz₀, hz₀r⟩
  obtain ⟨hzI, hz0⟩ := hz
  change r z = 0 at hz0
  have hzlt : z < 1 := lt_of_le_of_ne hzI.2 (by rintro rfl; linarith)
  obtain ⟨w, hw, hder⟩ := hzero z hzI hz0
  have hright := (hasDerivAt_iff_tendsto_slope_left_right.mp hder).2
  have hneg := hright.eventually_lt_const hw
  have hlt : ∀ᶠ t in 𝓝[>] z, t < 1 :=
    (eventually_lt_nhds hzlt).filter_mono nhdsWithin_le_nhds
  have himp : ∀ᶠ t in 𝓝[>] z, False := by
    filter_upwards [hneg, self_mem_nhdsWithin, hlt] with t hs hzt ht1
    change z < t at hzt
    rw [slope_def_field, hz0, sub_zero] at hs
    have htneg : r t < 0 := (div_neg_iff.mp hs).resolve_left (by
      rintro ⟨_, h⟩; linarith)
      |>.1
    obtain ⟨s, hsI, hsz⟩ := intermediate_value_Icc ht1.le hc.continuousOn
      (show 0 ∈ Icc (r t) (r 1) from ⟨htneg.le, hout.le⟩)
    have hsz' : s ∈ Z := ⟨⟨le_trans hzI.1 (le_trans hzt.le hsI.1), hsI.2⟩, hsz⟩
    linarith [hmax hsz', hsI.1]
  exact himp.exists.elim (fun _ h => h)

end
end NoHair.TwoCentre.Advanced

open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Advanced
open NoHair.TwoCentre.Advanced

/-- Across the selected future horizon the advanced metric and gauge potential
have analytic coefficients. The radial block has determinant −1, matches the
advanced expression on the exterior, and timelike curves can only cross inward. -/
theorem checkedResult :
    (∀ p : ℝ × ℝ, |p.1| < 1 / 4 → |p.2| ≤ 1 →
      0 < H p ∧
      (∀ f ∈ [gvv, gvr, grr, angularScale, potentialV, potentialR], AnalyticAt ℝ f p) ∧
      gvv p * grr p - gvr p ^ 2 = -1 ∧
      (0 < p.1 → grr p = (H p ^ 4 - H₀ p ^ 4) / (p.1 ^ 2 * H p ^ 2) ∧
        potentialR p = -(H₀ p ^ 2 / (p.1 * H p)) + H₀ p / p.1)) ∧
    (∀ c : ℝ, gvv (0, c) = 0 ∧ gvr (0, c) = 1 ∧ grr (0, c) = c ∧ angularScale (0, c) = 1) ∧
    (∀ r : ℝ → ℝ, Continuous r → r 0 ≤ 0 →
      (∀ t ∈ Icc (0 : ℝ) 1, r t = 0 → ∃ b v w a : ℝ, HasDerivAt r w t ∧ 0 ≤ a ∧
        2 * v * w + b * w ^ 2 + a < 0 ∧ -v + (1 - b) * w / 2 < 0) → r 1 ≤ 0) := by
  refine ⟨?_, horizon_values, ?_⟩
  · intro p hr hc
    obtain ⟨harg, _, hH⟩ := collar_positive hr hc
    have hgap := gap_factor harg
    exact ⟨hH, coefficient_analytic harg hH, determinant hH.ne' hgap,
      fun h => match_exterior h.ne' hH.ne' hgap⟩
  · intro r hc hin hcurve
    apply no_outward_crossing hc _ hin
    intro t ht hz
    obtain ⟨b, v, w, a, hd, ha, htime, hfuture⟩ := hcurve t ht hz
    exact ⟨w, future_radial_negative ha htime hfuture, hd⟩
end ElectrovacProof001

alias NoHair.TwoCentre.Advanced.regular_horizon := ElectrovacProof001.checkedResult


namespace ElectrovacProof002

open _root_.NoHair _root_.NoHair.TwoCentre
open NoHair NoHair.TwoCentre Set Topology
open scoped ContDiff Manifold

namespace NoHair.TwoCentre.Cartesian
open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Cartesian

export _root_.TwoCentreEndCoordinates.NoHair.TwoCentre.Cartesian (coordinates_time)

export _root_.TwoCentreEndCoordinates.NoHair.TwoCentre.Cartesian (coordinates_spatial)

export _root_.TwoCentreEndCoordinates.NoHair.TwoCentre.Cartesian (coordinates_recover)

export _root_.TwoCentreEndCoordinates.NoHair.TwoCentre.Cartesian (spatial_smooth)

export _root_.TwoCentreEndCoordinates.NoHair.TwoCentre.Cartesian (coordinates_smooth)

noncomputable def splitHomeo : E4 ≃ₜ ℝ × E3 where
  toFun y := (y 0, spatial y)
  invFun p := coordinates p.1 p.2
  left_inv := coordinates_recover
  right_inv := fun ⟨t, x⟩ => Prod.ext (coordinates_time t x) (coordinates_spatial t x)
  continuous_toFun := ((contDiff_piLp_apply (p := 2) (i := (0 : Fin 4))
    (𝕜 := ℝ) (n := ∞)).continuous).prodMk spatial_smooth.continuous
  continuous_invFun := coordinates_smooth.continuous

export _root_.TwoCentreEndCoordinates.NoHair.TwoCentre.Cartesian (unit_norm)

export _root_.TwoCentreEndCoordinates.NoHair.TwoCentre.Cartesian (norm_squared)

export _root_.TwoCentreEndCoordinates.NoHair.TwoCentre.Cartesian (exterior_iff)

export _root_.TwoCentreEndCoordinates.NoHair.TwoCentre.Cartesian (expanded_norm)

export _root_.TwoCentreEndCoordinates.NoHair.TwoCentre.Cartesian (contracted_norm)

export _root_.TwoCentreEndCoordinates.NoHair.TwoCentre.Cartesian (contract_expand)

export _root_.TwoCentreEndCoordinates.NoHair.TwoCentre.Cartesian (expand_contract)

export _root_.TwoCentreEndCoordinates.NoHair.TwoCentre.Cartesian (pole_contract)

export _root_.TwoCentreEndCoordinates.NoHair.TwoCentre.Cartesian (pole_expand)

export _root_.TwoCentreEndCoordinates.NoHair.TwoCentre.Cartesian (shift_smooth)

export _root_.TwoCentreEndCoordinates.NoHair.TwoCentre.Cartesian (toAdvanced_smooth)

export _root_.TwoCentreEndCoordinates.NoHair.TwoCentre.Cartesian (toIsotropic_smooth)

export _root_.TwoCentreEndCoordinates.NoHair.TwoCentre.Cartesian (global_chart)

theorem spacetime_open : IsOpen spacetime :=
  (isOpen_lt continuous_const spatial_smooth.continuous.norm).inter
    (isOpen_ne_fun spatial_smooth.continuous continuous_const)

theorem shell_in_spacetime {z : E4} (hz : z ∈ horizon) : z ∈ spacetime := by
  change ‖spatial z‖ = 1 at hz
  refine ⟨by linarith, ?_⟩
  intro he
  rw [he, norm_smul, unit_norm, mul_one] at hz
  norm_num at hz

theorem frontier_shell :
    frontier {z : spacetime | (z : E4) ∈ outerRegion} = {z : spacetime | (z : E4) ∈ horizon} := by
  let P : spacetime → E3 := fun z => spatial z.val
  have hop : IsOpenMap P := (isOpenMap_snd.comp splitHomeo.isOpenMap).comp
    spacetime_open.isOpenMap_subtype_val
  have hc : Continuous P := spatial_smooth.continuous.comp continuous_subtype_val
  have he : {z : spacetime | (z : E4) ∈ outerRegion} = P ⁻¹' (Metric.closedBall (0 : E3) 1)ᶜ := by
    ext z
    simp only [mem_ofPred_eq, outerRegion, mem_preimage, mem_compl_iff, Metric.mem_closedBall,
      dist_zero_right, not_le, P]
    exact and_iff_left z.property.2
  rw [he, ← hop.preimage_frontier_eq_frontier_preimage hc, frontier_compl,
    frontier_closedBall (0 : E3) (by norm_num : (1 : ℝ) ≠ 0)]
  ext z
  simp [P, horizon]

theorem connected_shell : IsConnected {z : spacetime | (z : E4) ∈ horizon} := by
  have hdim : 1 < Module.rank ℝ E3 := Module.one_lt_rank_of_one_lt_finrank (by
    rw [finrank_euclideanSpace_fin]; decide)
  have hs := (isConnected_univ (α := ℝ)).prod (isConnected_sphere hdim (0 : E3) zero_le_one)
  have he : splitHomeo.symm '' ((univ : Set ℝ) ×ˢ Metric.sphere (0 : E3) 1) = horizon := by
    rw [Homeomorph.image_symm]
    ext y
    simp [splitHomeo, horizon]
  have hconn : IsConnected horizon := he ▸ hs.image _ splitHomeo.symm.continuous.continuousOn
  have him : Subtype.val '' {z : spacetime | (z : E4) ∈ horizon} = horizon := by
    ext y
    exact ⟨fun ⟨z, hz, hzy⟩ => hzy ▸ hz, fun hy => ⟨⟨y, shell_in_spacetime hy⟩, hy, rfl⟩⟩
  have hi : IsConnected (Subtype.val '' {z : spacetime | (z : E4) ∈ horizon}) := by
    rw [him]
    exact hconn
  exact ⟨image_nonempty.mp hi.nonempty, Topology.IsInducing.subtypeVal.isPreconnected_image.mp hi.isPreconnected⟩

end NoHair.TwoCentre.Cartesian

open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Cartesian
open NoHair.TwoCentre.Cartesian

/-- One open Cartesian coordinate manifold contains a complete copy of the
two-centre exterior and the collar at its left pole. Its exterior has exactly
one connected frontier, the unit sphere of each advanced time slice. -/
theorem checkedResult :
    IsOpen spacetime ∧ IsDiffeoOnto toAdvanced exterior outerRegion ∧
    frontier {z : spacetime | (z : E4) ∈ outerRegion} = {z : spacetime | (z : E4) ∈ horizon} ∧
    IsConnected {z : spacetime | (z : E4) ∈ horizon} := by
  exact ⟨spacetime_open, global_chart, frontier_shell, connected_shell⟩
end ElectrovacProof002

alias NoHair.TwoCentre.Cartesian.exterior_and_frontier := ElectrovacProof002.checkedResult


namespace ElectrovacProof003

open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Cartesian _root_.NoHair.TwoCentre.Model
open NoHair NoHair.TwoCentre NoHair.TwoCentre.Cartesian NoHair.TwoCentre.Model Set Topology
open scoped ContDiff Manifold RealInnerProductSpace

namespace NoHair.TwoCentre.Model.Curves
open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Model

noncomputable section

export _root_.TwoCentreEndTensorPullbacks.NoHair.TwoCentre.Model.Curves (radialSpeed)

export _root_.TwoCentreEndTensorPullbacks.NoHair.TwoCentre.Model.Curves (spatial_inner)

export _root_.TwoCentreEndTensorPullbacks.NoHair.TwoCentre.Model.Curves (radialSpeed_coords)

export _root_.TwoCentreEndTensorPullbacks.NoHair.TwoCentre.Model.Curves (metric_eval)

theorem angular_unit (z : manifold) : ‖angularDirection z‖ = 1 := by
  have hz : (3 : ℝ) / 4 < ‖spatial z‖ := z.property.1
  have hpos : 0 < ‖spatial z‖ := by linarith
  rw [angularDirection, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos), inv_mul_cancel₀ hpos.ne']


end
end NoHair.TwoCentre.Model.Curves

namespace NoHair.TwoCentre.Advanced
open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Advanced
noncomputable section
export _root_.TwoCentreEndTensorPullbacks.NoHair.TwoCentre.Advanced (gap_factor)

export _root_.TwoCentreEndTensorPullbacks.NoHair.TwoCentre.Advanced (coefficient_analytic)

export _root_.ElectrovacProof001.NoHair.TwoCentre.Advanced (determinant)

export _root_.TwoCentreEndTensorPullbacks.NoHair.TwoCentre.Advanced (match_exterior)

end
end NoHair.TwoCentre.Advanced

open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Cartesian _root_.NoHair.TwoCentre.Model
open NoHair NoHair.TwoCentre NoHair.TwoCentre.Cartesian NoHair.TwoCentre.Model Set Filter Topology
open scoped Manifold ContDiff RealInnerProductSpace BigOperators
namespace NoHair.TwoCentre.Model.Geo
open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Model
noncomputable section

abbrev Mat4 := Matrix (Fin 4) (Fin 4) ℝ
export _root_.TwoCentreEndTensorPullbacks.NoHair.TwoCentre.Model.Geo (AM)

export _root_.TwoCentreEndTensorPullbacks.NoHair.TwoCentre.Model.Geo (spatial_an)

export _root_.TwoCentreEndTensorPullbacks.NoHair.TwoCentre.Model.Geo (coordinate_an)

theorem coords_self (z : E4) : coordinates (z 0) (spatial z) = z := by
  ext i; exact Fin.cases rfl (fun _ => rfl) i

export _root_.TwoCentreEndTensorPullbacks.NoHair.TwoCentre.Model.Geo (partial_an)

export _root_.TwoCentreEndTensorPullbacks.NoHair.TwoCentre.Model.Geo (unit_inner)

export _root_.TwoCentreEndTensorPullbacks.NoHair.TwoCentre.Model.Geo (param_norm)

export _root_.TwoCentreEndTensorPullbacks.NoHair.TwoCentre.Model.Geo (radius_data)

export _root_.TwoCentreEndTensorPullbacks.NoHair.TwoCentre.Model.Geo (reg_data)

theorem matrix_basis (A : Mat4) (i j : Fin 4) : matrixBilin A (coordBasis i) (coordBasis j) = A i j := by
  change Matrix.toLinearMap₂' ℝ A (WithLp.ofLp (coordBasis i)) (WithLp.ofLp (coordBasis j)) = A i j
  simp only [coordBasis, EuclideanSpace.single, PiLp.ofLp_single]
  rw [Matrix.toLinearMap₂'_apply]
  simp_rw [← Finset.smul_sum]
  simp [Pi.single_apply, Finset.sum_ite_eq']

theorem atlas_id {c : OpenPartialHomeomorph manifold E4} (hc : c ∈ atlas E4 manifold) {y : E4}
    (hy : y ∈ c.target) :
    (c.symm y : E4) = y ∧ (mfderiv 𝓘(ℝ,E4) 𝓘(ℝ,E4) c.symm y : E4 →L[ℝ] E4) = ContinuousLinearMap.id ℝ E4 := by
  obtain ⟨p,hp⟩ := TopologicalSpace.Opens.chart_eq (H := E4) ⟨c.symm y⟩ hc
  have hchart (x : manifold) : c = chartAt E4 x := hp.trans (by rfl)
  have hval : (c.symm y : E4) = y := by
    have eqval (x : manifold) : c x = x.val := by rw [hchart x]; rfl
    exact (eqval (c.symm y)).symm.trans (c.right_inv hy)
  refine ⟨hval,?_⟩
  have d := mfderivWithin_range_extChartAt_symm (I := 𝓘(ℝ,E4)) (x := c.symm y)
  simp only [modelWithCornersSelf_coe,range_id,mfderivWithin_univ] at d
  rw [hchart (c.symm y), ← hval]
  exact d

theorem smooth_of_components (A : E4 → Mat4) (hA : ∀ z : manifold, ∀ i j, AM (fun y => A y i j) z) :
    IsSmoothBilinField (fun z : manifold => matrixBilin (A z)) := by
  intro c hc i j y hy
  have hh : EqOn (fun w => pullbackCoeffs (M := manifold) (fun z => matrixBilin (A z)) c.symm w i j)
      (fun w => A w i j) c.target := by
    intro w hw
    obtain ⟨hv,hder⟩ := atlas_id hc hw
    change pullbackCoeffs (M := manifold) (fun z => matrixBilin (A z)) c.symm w i j = A w i j
    unfold pullbackCoeffs
    rw [hder]
    change matrixBilin (A (c.symm w : E4)) (coordBasis i) (coordBasis j) = A w i j
    rw [hv,matrix_basis]
  have hf := (hA (c.symm y) i j).of_le (show (∞ : ℕ∞ω) ≤ ω by simp)
  rw [(atlas_id hc hy).1] at hf
  exact hf.contDiffWithinAt.congr_of_eventuallyEq (hh.eventuallyEq_of_mem (c.open_target.mem_nhds hy) |>.filter_mono nhdsWithin_le_nhds) (hh hy)

theorem antisymmetric : IsTwoForm faraday := by
  intro z v w
  let A : Mat4 := faradayCoeffs z
  change Matrix.toLinearMap₂' ℝ A (WithLp.ofLp (v : E4)) (WithLp.ofLp (w : E4)) =
    -Matrix.toLinearMap₂' ℝ A (WithLp.ofLp (w : E4)) (WithLp.ofLp (v : E4))
  rw [Matrix.toLinearMap₂'_apply (R := ℝ) A (WithLp.ofLp (v : E4)) (WithLp.ofLp (w : E4)),
    Matrix.toLinearMap₂'_apply (R := ℝ) A (WithLp.ofLp (w : E4)) (WithLp.ofLp (v : E4))]
  simp only [Fin.sum_univ_four, smul_eq_mul, A, faradayCoeffs]
  ring

end
end NoHair.TwoCentre.Model.Geo

open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Cartesian _root_.NoHair.TwoCentre.Model
open NoHair NoHair.TwoCentre NoHair.TwoCentre.Cartesian NoHair.TwoCentre.Model Set Filter Topology
open scoped Manifold ContDiff RealInnerProductSpace BigOperators

namespace NoHair.TwoCentre.Model.Geo
open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Model
noncomputable section

theorem frame_metric (z : manifold) :
    ∃ liftV : E4 → E4, ∀ v w, metric z (liftV v) (liftV w) = -(v 0*w 0) + ⟪spatial v,spatial w⟫ := by
  obtain ⟨hρ,harg,hH,hH0⟩ := radius_data z
  let p := parameters z
  let a := Advanced.gvv p
  let b := Advanced.gvr p
  let d := Advanced.grr p
  let n := angularDirection z
  let k := ‖spatial z‖ / Advanced.H p
  let ℓ := d / (b+1)
  have hb : 0 < b := div_pos (sq_pos_of_pos hH0) (sq_pos_of_pos hH)
  have hdet : a*d - b^2 = -1 := Advanced.determinant hH.ne' (Advanced.gap_factor harg)
  have hℓ₁ : a*ℓ = b-1 := by dsimp [ℓ];field_simp [show b+1≠0 by linarith];nlinarith
  have hℓ₂ : (b+1)*ℓ=d := by dsimp [ℓ]; field_simp [show b+1≠0 by linarith]
  have hnn : ⟪n,n⟫ = 1 := by rw [real_inner_self_eq_norm_sq, show ‖n‖=1 from param_norm hρ];norm_num
  let R := fun v : E4 => ⟪n,spatial v⟫
  let P := fun v : E4 => spatial v - R v • n
  let U := fun v : E4 => v 0 + R v
  let W := fun v : E4 => (R v - v 0 - a*U v)/2
  let V := fun v : E4 => U v - ℓ*W v
  let liftV := fun v : E4 => coordinates (V v) (W v • n + k • P v)
  have hp (v : E4) : ⟪n,P v⟫ = 0 := by simp only [P,R,inner_sub_right,real_inner_smul_right,hnn,mul_one,sub_self]
  have hpp (v w : E4) : ⟪P v,P w⟫ = ⟪spatial v,spatial w⟫ - R v*R w := by
    simp only [P,inner_sub_left,inner_sub_right,real_inner_smul_left,real_inner_smul_right,hnn,
      real_inner_comm (spatial v) n,R]
    ring
  have hspace (v : E4) : spatial (liftV v) = W v • n + k • P v := spatial_coordinates _ _
  have hr (v : E4) : Curves.radialSpeed z (liftV v) = W v := by
    change ⟪n,spatial (liftV v)⟫ = W v
    rw [hspace,inner_add_right,real_inner_smul_right,real_inner_smul_right,hnn,hp]
    ring
  have hpair (v w : E4) : ⟪spatial (liftV v),spatial (liftV w)⟫- W v*W w =
      k^2*(⟪spatial v,spatial w⟫-R v*R w) := by
    rw [hspace,hspace]
    have hpn : ⟪P v,n⟫ = 0 := (real_inner_comm _ _).trans (hp v)
    simp only [inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right,hnn,hp,
      hpn,hpp]
    ring
  have scale : Advanced.angularScale p / ‖spatial z‖ ^ 2 * k^2 = 1 := by
    have hHp : Advanced.H p ≠ 0 := hH.ne'
    dsimp only [Advanced.angularScale,k];field_simp [hHp,hρ.ne']
  refine ⟨liftV,?_⟩
  intro v w
  rw [Curves.metric_eval,hr,hr,hpair]
  change a*V v*V w + b*(V v*W w+W v*V w)+d*W v*W w +
    (Advanced.angularScale p / ‖spatial z‖^2)*(k^2*_) = _
  rw [← mul_assoc,scale,one_mul]
  have ht : a*V v*V w+b*(V v*W w+W v*V w)+d*W v*W w =
      a*U v*U w + U v*W w + W v*U w := by
    change a*(U v-ℓ*W v)*(U w-ℓ*W w)+b*((U v-ℓ*W v)*W w+W v*(U w-ℓ*W w))+d*W v*W w = _
    linear_combination (-U v*W w-W v*U w+ℓ*W v*W w)*hℓ₁ - (W v*W w)*hℓ₂
  rw [ht]
  dsimp [U,W]
  ring

theorem lorentzian : IsLorentzian metric := by
  intro z
  obtain ⟨liftV, h⟩ := frame_metric z
  let B : E4 →L[ℝ] E4 →L[ℝ] ℝ := metric z
  let f := fun i => liftV (coordBasis i)
  have orth (i j : Fin 4) : B (f i) (f j) = minkowski i j := by
    change metric z (liftV (coordBasis i)) (liftV (coordBasis j)) = _
    rw [h,Curves.spatial_inner]
    fin_cases i <;> fin_cases j <;> simp (config := {decide := true}) [coordBasis,minkowski,Matrix.diagonal]
  have independent : LinearIndependent ℝ f := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have eq := congrArg (fun x : E4 => B (f j) x) hc
    simp only [map_sum,map_smul,orth,smul_eq_mul,map_zero] at eq
    fin_cases j <;> simpa [Fin.sum_univ_four,minkowski,Matrix.diagonal] using eq
  have hc : Fintype.card (Fin 4) = Module.finrank ℝ E4 := by simp
  let basis := basisOfLinearIndependentOfCardEqFinrank independent hc
  refine ⟨basis,?_⟩
  intro i j
  change B (basis i) (basis j) = _
  simpa [basis,coe_basisOfLinearIndependentOfCardEqFinrank] using orth i j

theorem orientation_valid : IsTimeOrientation metric orientation := by
  constructor
  · apply continuous_iff_continuousAt.mpr
    intro z
    apply (FiberBundle.continuousAt_section E4 z).2
    have he (x : manifold) : (trivializationAt E4 (TangentSpace 𝓘(ℝ,E4)) z
        (⟨x,orientation x⟩ : TangentBundle 𝓘(ℝ,E4) manifold)).2 = (orientation x : E4) := by
      change tangentCoordChange 𝓘(ℝ,E4) x z x (orientation x) = orientation x
      have same : achart E4 z = achart E4 x := by rfl
      unfold tangentCoordChange
      rw [same]
      exact (tangentBundleCore 𝓘(ℝ,E4) manifold).coordChange_self (achart E4 x) x (mem_achart_source E4 x) _
    simp_rw [he]
    exact (reg_data z).2.2.2.continuousAt.comp continuous_subtype_val.continuousAt
  · intro z
    obtain ⟨hρ,_,hH,hH0⟩ := radius_data z
    let p := parameters z
    let α := Advanced.gvr p/(1+Advanced.grr p^2)
    have hb : 0 < Advanced.gvr p := div_pos (sq_pos_of_pos hH0) (sq_pos_of_pos hH)
    have hα : 0 < α := div_pos hb (by positivity)
    have ha0 : Advanced.gvv p ≤ 0 := div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (sq_nonneg _)
    let T : E4 := orientation z
    change metric z T T < 0
    have hT : spatial T = -α • angularDirection z := spatial_coordinates _ _
    have hr : Curves.radialSpeed z T = -α := by
      change ⟪angularDirection z, spatial T⟫ = -α
      rw [hT,real_inner_smul_right,real_inner_self_eq_norm_sq,Curves.angular_unit]
      ring
    have hss : ⟪spatial T,spatial T⟫ = α^2 := by
      rw [hT,real_inner_smul_left,real_inner_smul_right,real_inner_self_eq_norm_sq,Curves.angular_unit]
      ring
    rw [Curves.metric_eval,hr,hss]
    change Advanced.gvv p * 1 * 1 + Advanced.gvr p*(1 * -α + -α*1)+Advanced.grr p*(-α)*(-α) + _*(α^2-(-α)*(-α)) < 0
    have hrel : α*(1+Advanced.grr p^2) = Advanced.gvr p := by dsimp [α];field_simp
    have hle : Advanced.grr p ≤ 1+Advanced.grr p^2 := by nlinarith [sq_nonneg (Advanced.grr p-1/2)]
    nlinarith [mul_le_mul_of_nonneg_left hle (sq_nonneg α),mul_pos hα hb,congrArg (α * ·) hrel]

end
end NoHair.TwoCentre.Model.Geo

open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Cartesian _root_.NoHair.TwoCentre.Model
open NoHair NoHair.TwoCentre NoHair.TwoCentre.Cartesian NoHair.TwoCentre.Model Set Filter Topology
open scoped Manifold ContDiff RealInnerProductSpace BigOperators
namespace NoHair.TwoCentre.Model.Geo
open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Model
noncomputable section

theorem spatial_shift (s : ℝ) (z : E4) : spatial (z+s • coordBasis 0) = spatial z := by
  ext i; simp [spatial,coordBasis]

theorem flow_val (s : ℝ) (z : manifold) : (flow s z : E4) = (z:E4) + s • coordBasis 0 := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [flow,coordBasis,coordinates,spatial]

export _root_.TwoCentreEndTensorPullbacks.NoHair.TwoCentre.Model.Geo (val_diff)

theorem flow_smooth :
    ContMDiff (𝓘(ℝ,ℝ).prod 𝓘(ℝ,E4)) 𝓘(ℝ,E4) ∞ (fun p : ℝ × manifold => flow p.1 p.2) := by
  apply (ContMDiff.subtypeVal_comp_iff manifold _).1
  change ContMDiff _ _ _ (fun p : ℝ × manifold => (flow p.1 p.2 : E4))
  simp only [flow_val]
  exact (contMDiff_subtype_val.comp contMDiff_snd).add (contMDiff_fst.smul contMDiff_const)

set_option backward.isDefEq.respectTransparency false in
theorem flow_diff (s : ℝ) (z : manifold) : (mfderiv 𝓘(ℝ,E4) 𝓘(ℝ,E4) (flow s) z : E4 →L[ℝ] E4) =
    ContinuousLinearMap.id ℝ E4 := by
  have hs : ContMDiff 𝓘(ℝ,E4) 𝓘(ℝ,E4) ∞ (flow s) :=
    flow_smooth.comp (contMDiff_const.prodMk contMDiff_id)
  have h := (val_diff (flow s z)).comp z (hs.mdifferentiableAt (by simp)).hasMFDerivAt
  have ht : HasFDerivAt (fun x : E4 => x+s • coordBasis 0) (ContinuousLinearMap.id ℝ E4) (z:E4) :=
    (hasFDerivAt_id _).add_const _
  have hot := (hasMFDerivAt_iff_hasFDerivAt.mpr ht).comp z (val_diff z)
  have he : (Subtype.val ∘ flow s : manifold → E4) = (fun x : E4 => x+s • coordBasis 0) ∘ Subtype.val := funext (flow_val s)
  rw [he] at h
  exact h.mfderiv.symm.trans hot.mfderiv

set_option backward.isDefEq.respectTransparency false in
theorem flow_gen (z : manifold) : (flowGenerator flow z : E4) = coordBasis 0 := by
  have hs : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,E4) ∞ (fun s : ℝ => flow s z) :=
    flow_smooth.comp (contMDiff_id.prodMk contMDiff_const)
  have h := (val_diff (flow 0 z)).comp 0 (hs.mdifferentiableAt (by simp)).hasMFDerivAt
  have ht : HasDerivAt (fun s : ℝ => (z:E4)+s • coordBasis 0) (coordBasis 0) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (coordBasis 0)).const_add (z:E4)
  have he : (Subtype.val ∘ (fun s : ℝ => flow s z) : ℝ → E4) = fun s => (z:E4)+s • coordBasis 0 :=
    funext (fun s => flow_val s z)
  rw [he] at h
  exact (hasMFDerivAt_iff_hasFDerivAt.mp h).hasDerivAt.unique ht

theorem flow_symmetry : IsSymmetryFlow metric faraday flow := by
  have pot (s : ℝ) (i : Fin 4) (z : E4) : potential i (z+s • coordBasis 0) = potential i z := by
    simp [potential,parameters,dr,angularDirection,spatial_shift]
  have dpot (s : ℝ) (i j : Fin 4) (z : E4) : coordPartial (potential i) j (z+s • coordBasis 0) =
      coordPartial (potential i) j z := by
    apply congrArg (fun L : E4 →L[ℝ] ℝ => L (coordBasis j))
    rw [← fderiv_comp_add_right (f := potential i) (s • coordBasis 0), funext (pot s i)]
  refine ⟨?_,?_,flow_smooth,?_,?_⟩
  · intro z; apply Subtype.ext; simp [flow_val]
  · intro s t z; apply Subtype.ext; simp only [flow_val,add_smul]; abel
  · intro s z v w
    rw [flow_diff]
    change matrixBilin (metricCoeffs (flow s z)) v w = matrixBilin (metricCoeffs z) v w
    have he : metricCoeffs (flow s z) = metricCoeffs z := by funext i j; simp [flow_val,metricCoeffs,dr,parameters,angularDirection,spatial_shift]
    rw [he]
  · intro s z v w
    rw [flow_diff]
    change matrixBilin (faradayCoeffs (flow s z)) v w = matrixBilin (faradayCoeffs z) v w
    have he : faradayCoeffs (flow s z) = faradayCoeffs z := by funext i j; simp [flow_val,faradayCoeffs,dpot]
    rw [he]

export _root_.TwoCentreEndTensorPullbacks.NoHair.TwoCentre.Model.Geo (line_deriv)

export _root_.TwoCentreEndTensorPullbacks.NoHair.TwoCentre.Model.Geo (spatialL)

export _root_.TwoCentreEndTensorPullbacks.NoHair.TwoCentre.Model.Geo (norm_der)

export _root_.TwoCentreEndTensorPullbacks.NoHair.TwoCentre.Model.Geo (shift_der)

export _root_.TwoCentreEndTensorPullbacks.NoHair.TwoCentre.Model.Geo (partial_from_line)

export _root_.TwoCentreEndTensorPullbacks.NoHair.TwoCentre.Model.Geo (second_symm)

def staticTime (z : E4) := z 0-timeShift (‖spatial z‖-1)
theorem outer_open : IsOpen outerRegion := (isOpen_lt continuous_const spatial_an.continuous.norm).inter
  (isOpen_ne_fun spatial_an.continuous continuous_const)

theorem time_an {z : E4} (hz : z ∈ outerRegion) : AM staticTime z := by
  have hs : 0 < ‖spatial z‖ := by linarith [hz.1]
  have hnr := spatial_an.contDiffAt.norm ℝ (norm_pos_iff.mp hs)
  have hr : ‖spatial z‖ - 1 ≠ 0 := (sub_pos.mpr hz.1).ne'
  have hf : ContDiffAt ℝ ω timeShift (‖spatial z‖-1) := by unfold timeShift;fun_prop (disch := assumption)
  have hnr2 : ContDiffAt ℝ ω (fun x => ‖spatial x‖ - 1) z := hnr.sub contDiffAt_const
  have hh := ContDiffAt.comp (g := timeShift) (f := fun x : E4 => ‖spatial x‖-1) z hf hnr2
  exact (contDiffAt_piLp_apply (p := 2) (i := (0:Fin 4))).sub hh

theorem time_partial {z : E4} (hz : z ∈ outerRegion) (i : Fin 4) :
    coordPartial staticTime i z = dt i - (Advanced.H₀ (parameters z)^2/(‖spatial z‖-1)^2) * dr z i := by
  let v := coordBasis i
  let x := fun t : ℝ => z+t • v
  have hx := line_deriv z v
  have hx0 : x 0 = z := by simp [x]
  have hxs := spatialL.hasFDerivAt.comp_hasDerivAt 0 hx
  have hn : 0 < ‖spatial (x 0)‖ := by rw [hx0];linarith [hz.1]
  have hr := (norm_der (f := fun t => spatial (x t)) hxs hn).sub_const 1
  have hshift := (shift_der (r := ‖spatial (x 0)‖-1) (by rw [hx0];exact (sub_pos.mpr hz.1).ne')).comp 0 hr
  have ht := (PiLp.proj (p := 2) (β := fun _ : Fin 4 => ℝ) 0).hasFDerivAt.comp_hasDerivAt 0 hx
  apply partial_from_line (time_an hz |>.differentiableAt (by simp))
  convert! ht.sub hshift using 1
  dsimp only [Function.comp_apply,spatialL] at *
  rw [hx0]
  have hrad : ⟪angularDirection z,spatial v⟫ = dr z i := by
    change Curves.radialSpeed z (coordBasis i) = dr z i
    have he := Curves.spatial_inner (coordinates 0 (angularDirection z)) (coordBasis i)
    rw [spatial_coordinates] at he
    change ⟪angularDirection z,spatial (coordBasis i)⟫ = _
    rw [he]
    fin_cases i <;> simp (config := {decide := true}) [coordBasis,dr,coordinates] <;> rfl
  have ht0 : v 0 = dt i := by fin_cases i <;> simp [v,dt,coordBasis]
  change _ = v 0 - ((1 + 3/2 * (‖spatial z‖-1))^2 / (‖spatial z‖-1)^2) * ⟪angularDirection z,spatial v⟫
  rw [hrad,ht0]
  rfl

theorem partial_prod {f g : E4 → ℝ} {y : E4} (hf : DifferentiableAt ℝ f y)
    (hg : DifferentiableAt ℝ g y) (i : Fin 4) :
    coordPartial (fun z => f z * g z) i y = coordPartial f i y * g y + f y * coordPartial g i y := by
  have h := DFunLike.congr_fun (hf.hasFDerivAt.mul hg.hasFDerivAt).fderiv (coordBasis i)
  change fderiv ℝ (f * g) y (coordBasis i) = _
  rw [h]
  simp [coordPartial,smul_eq_mul]
  <;> ring

theorem staticity : IsStaticOn metric flow outer := by
  intro c hc y hy ho l i j
  let k := fun z => loweredCoeffs metric (flowGenerator flow) c.symm z
  let a := fun z : E4 => Advanced.gvv (parameters z)
  have heq {w : E4} (hw : w ∈ c.target) (houter : w ∈ outerRegion) (i : Fin 4) :
      k w i = a w * coordPartial staticTime i w := by
    obtain ⟨hv,hd⟩ := atlas_id hc hw
    change metric (c.symm w) (flowGenerator flow (c.symm w)) (mfderiv 𝓘(ℝ,E4) 𝓘(ℝ,E4) c.symm w (coordBasis i)) = _
    rw [flow_gen,hd]
    change matrixBilin (metricCoeffs (c.symm w):Mat4) (coordBasis 0) (coordBasis i) = _
    rw [hv, matrix_basis (metricCoeffs w : Mat4),time_partial houter i]
    have hH := (radius_data (c.symm w)).2.2.1
    rw [hv] at hH
    have hr : ‖spatial w‖-1 ≠ 0 := (sub_pos.mpr houter.1).ne'
    have dr0 : dr w 0 = 0 := rfl
    have del : spatialDelta 0 i = 0 := by simp [spatialDelta]
    simp only [metricCoeffs,show dt 0=1 from rfl,dr0,del,zero_mul,mul_zero,mul_one,one_mul,add_zero,sub_zero,neg_zero]
    dsimp [a,Advanced.gvv,Advanced.gvr,parameters] at *
    field_simp [hr, hH.ne']
    <;> ring
  have houter : y ∈ outerRegion := (atlas_id hc hy).1 ▸ ho
  have hw := heq hy houter
  have ha : AM a y := by
    obtain ⟨_,harg,hH,_⟩ := radius_data (c.symm y)
    rw [(atlas_id hc hy).1] at harg hH
    have hs : 0 < ‖spatial y‖ := by linarith [houter.1]
    have hn := spatial_an.contDiffAt.norm ℝ (norm_pos_iff.mp hs)
    have dir : ContDiffAt ℝ ω angularDirection y := (hn.inv hs.ne').smul spatial_an.contDiffAt
    have hp : ContDiffAt ℝ ω parameters y := (hn.sub contDiffAt_const).prodMk ((contDiffAt_piLp_apply (p := 2) (i := (0:Fin 3))).comp y dir)
    exact ((Advanced.coefficient_analytic harg hH _ (by simp : Advanced.gvv ∈ _)).contDiffAt).comp y hp
  have htime := time_an houter
  have d (u v : Fin 4) : coordPartial (fun z => k z u) v y =
      coordPartial a v y * coordPartial staticTime u y + a y * coordPartial (coordPartial staticTime u) v y := by
    have ev : (fun z => k z u) =ᶠ[𝓝 y] (fun z => a z*coordPartial staticTime u z) := by
      filter_upwards [c.open_target.mem_nhds hy,outer_open.mem_nhds houter] with z h1 h2
      exact heq h1 h2 u
    exact (congrArg (fun L : E4 →L[ℝ] ℝ => L (coordBasis v)) ev.fderiv_eq).trans
      (partial_prod (ha.differentiableAt (by simp)) ((partial_an htime u).differentiableAt (by simp)) v)

  change k y l * (coordPartial (fun z => k z j) i y - coordPartial (fun z => k z i) j y) +
    k y i * (coordPartial (fun z => k z l) j y - coordPartial (fun z => k z j) l y) +
    k y j * (coordPartial (fun z => k z i) l y - coordPartial (fun z => k z l) i y) = 0
  simp only [d, hw]
  rw [second_symm htime j i,second_symm htime l j,second_symm htime i l]
  ring

end
end NoHair.TwoCentre.Model.Geo

open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Cartesian _root_.NoHair.TwoCentre.Model
open NoHair NoHair.TwoCentre NoHair.TwoCentre.Cartesian NoHair.TwoCentre.Model Set Filter Topology
open scoped Manifold ContDiff RealInnerProductSpace BigOperators
namespace NoHair.TwoCentre.Model.Geo
open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Model
noncomputable section

export _root_.TwoCentreEndTensorPullbacks.NoHair.TwoCentre.Model.Geo (sourceA)

export _root_.TwoCentreEndTensorPullbacks.NoHair.TwoCentre.Model.Geo (sourceR)

export _root_.TwoCentreEndTensorPullbacks.NoHair.TwoCentre.Model.Geo (sourceN)

export _root_.TwoCentreEndTensorPullbacks.NoHair.TwoCentre.Model.Geo (sourceSpeed)

export _root_.TwoCentreEndTensorPullbacks.NoHair.TwoCentre.Model.Geo (dist_squared)

export _root_.TwoCentreEndTensorPullbacks.NoHair.TwoCentre.Model.Geo (exterior_open)

export _root_.TwoCentreEndTensorPullbacks.NoHair.TwoCentre.Model.Geo (left_pos)

export _root_.TwoCentreEndTensorPullbacks.NoHair.TwoCentre.Model.Geo (source_unit)

export _root_.TwoCentreEndTensorPullbacks.NoHair.TwoCentre.Model.Geo (adv_spatial)

export _root_.TwoCentreEndTensorPullbacks.NoHair.TwoCentre.Model.Geo (adv_norm)

export _root_.TwoCentreEndTensorPullbacks.NoHair.TwoCentre.Model.Geo (adv_direction)

export _root_.TwoCentreEndTensorPullbacks.NoHair.TwoCentre.Model.Geo (adv_params)

export _root_.TwoCentreEndTensorPullbacks.NoHair.TwoCentre.Model.Geo (source_recover)

export _root_.TwoCentreEndTensorPullbacks.NoHair.TwoCentre.Model.Geo (adv_H)

export _root_.TwoCentreEndTensorPullbacks.NoHair.TwoCentre.Model.Geo (adv_mem)

export _root_.TwoCentreEndTensorPullbacks.NoHair.TwoCentre.Model.Geo (chart_coe)

export _root_.TwoCentreEndTensorPullbacks.NoHair.TwoCentre.Model.Geo (r_an)

export _root_.TwoCentreEndTensorPullbacks.NoHair.TwoCentre.Model.Geo (adv_an)

set_option backward.isDefEq.respectTransparency false in
export _root_.TwoCentreEndTensorPullbacks.NoHair.TwoCentre.Model.Geo (chart_der)

export _root_.TwoCentreEndTensorPullbacks.NoHair.TwoCentre.Model.Geo (packL)

export _root_.TwoCentreEndTensorPullbacks.NoHair.TwoCentre.Model.Geo (r_line)

export _root_.TwoCentreEndTensorPullbacks.NoHair.TwoCentre.Model.Geo (adv_der)

export _root_.TwoCentreEndTensorPullbacks.NoHair.TwoCentre.Model.Geo (J)

export _root_.TwoCentreEndTensorPullbacks.NoHair.TwoCentre.Model.Geo (velocity_data)

export _root_.TwoCentreEndTensorPullbacks.NoHair.TwoCentre.Model.Geo (tangential_pull)

export _root_.TwoCentreEndTensorPullbacks.NoHair.TwoCentre.Model.Geo (model_metric_pull)

export _root_.TwoCentreEndTensorPullbacks.NoHair.TwoCentre.Model.Geo (metric_chart)

export _root_.TwoCentreEndTensorPullbacks.NoHair.TwoCentre.Model.Geo (gauge)

export _root_.TwoCentreEndTensorPullbacks.NoHair.TwoCentre.Model.Geo (gauge_an)

export _root_.TwoCentreEndTensorPullbacks.NoHair.TwoCentre.Model.Geo (gauge_partial)

export _root_.TwoCentreEndTensorPullbacks.NoHair.TwoCentre.Model.Geo (potential_eval)

export _root_.TwoCentreEndTensorPullbacks.NoHair.TwoCentre.Model.Geo (potential_chart)

end
end NoHair.TwoCentre.Model.Geo

open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Cartesian _root_.NoHair.TwoCentre.Model
open NoHair NoHair.TwoCentre NoHair.TwoCentre.Cartesian NoHair.TwoCentre.Model Set Filter Topology
open scoped Manifold ContDiff RealInnerProductSpace BigOperators
namespace NoHair.TwoCentre.Model.Calc
open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Model
noncomputable section

export _root_.TwoCentreEndTensorPullbacks.NoHair.TwoCentre.Model.Calc (AM)

export _root_.TwoCentreEndTensorPullbacks.NoHair.TwoCentre.Model.Calc (jac)

export _root_.TwoCentreEndTensorPullbacks.NoHair.TwoCentre.Model.Calc (pull)

export _root_.TwoCentreEndTensorPullbacks.NoHair.TwoCentre.Model.Calc (curl)

export _root_.TwoCentreEndTensorPullbacks.NoHair.TwoCentre.Model.Calc (basis_expand)

export _root_.TwoCentreEndTensorPullbacks.NoHair.TwoCentre.Model.Calc (differential_expand)

export _root_.TwoCentreEndTensorPullbacks.NoHair.TwoCentre.Model.Calc (component_der)

export _root_.TwoCentreEndTensorPullbacks.NoHair.TwoCentre.Model.Calc (partial_mul)

export _root_.TwoCentreEndTensorPullbacks.NoHair.TwoCentre.Model.Calc (partial_sum)

export _root_.TwoCentreEndTensorPullbacks.NoHair.TwoCentre.Model.Calc (symmetric)

export _root_.TwoCentreEndTensorPullbacks.NoHair.TwoCentre.Model.Calc (exterior_derivative_pull)

end
end NoHair.TwoCentre.Model.Calc
open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Cartesian _root_.NoHair.TwoCentre.Model
open NoHair NoHair.TwoCentre NoHair.TwoCentre.Cartesian NoHair.TwoCentre.Model Set Filter Topology
open scoped ContDiff Manifold BigOperators
namespace NoHair.TwoCentre.Model.Geo
open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Model
noncomputable section

export _root_.TwoCentreEndTensorPullbacks.NoHair.TwoCentre.Model.Geo (electric_an)

export _root_.TwoCentreEndTensorPullbacks.NoHair.TwoCentre.Model.Geo (faraday_chart)

end
end NoHair.TwoCentre.Model.Geo

open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Model
open NoHair.TwoCentre.Model.Geo

theorem checkedResult :
    IsLorentzian metric ∧ IsSmoothBilinField metric ∧ IsSmoothBilinField faraday ∧
    IsTwoForm faraday ∧ IsTimeOrientation metric orientation ∧ IsSymmetryFlow metric faraday flow ∧
    IsStaticOn metric flow outer ∧ ∀ y ∈ exterior,
      pullbackCoeffs metric Model.chart y = isotropicMetric y ∧
      pullbackCoeffs faraday Model.chart y = TwoCentre.field y :=
  ⟨lorentzian, smooth_of_components metricCoeffs (fun z => (reg_data z).1),
    smooth_of_components faradayCoeffs (fun z => (reg_data z).2.2.1), antisymmetric,
    orientation_valid, flow_symmetry, staticity, fun _ hy => ⟨metric_chart hy,faraday_chart hy⟩⟩
end ElectrovacProof003

alias NoHair.TwoCentre.Model.stationary_geometry := ElectrovacProof003.checkedResult


section

open NoHair Set
open scoped ContDiff Manifold BigOperators Topology

private theorem partial_eq_on_open {s : Set E4} (hs : IsOpen s) {f g : E4 → ℝ}
    (h : EqOn f g s) (k : Fin 4) {z : E4} (hz : z ∈ s) :
    coordPartial f k z = coordPartial g k z :=
  congrArg (fun L : E4 →L[ℝ] ℝ => L (coordBasis k))
    (h.eventuallyEq_of_mem (hs.mem_nhds hz)).fderiv_eq

private theorem einsteinMaxwell_of_eqOn {s : Set E4} (hs : IsOpen s)
    {G' G F' F : E4 → Matrix (Fin 4) (Fin 4) ℝ}
    (hG : EqOn G' G s) (hF : EqOn F' F s) {y : E4} (hy : y ∈ s)
    (hem : EinsteinMaxwellAt G F y) : EinsteinMaxwellAt G' F' y := by
  have dG (z : E4) (hz : z ∈ s) (i j k : Fin 4) :
      coordPartial (fun w => G' w i j) k z = coordPartial (fun w => G w i j) k z :=
    partial_eq_on_open hs (fun w hw => congrArg (fun A : Matrix (Fin 4) (Fin 4) ℝ => A i j) (hG hw)) k hz
  have dF (z : E4) (hz : z ∈ s) (i j k : Fin 4) :
      coordPartial (fun w => F' w i j) k z = coordPartial (fun w => F w i j) k z :=
    partial_eq_on_open hs (fun w hw => congrArg (fun A : Matrix (Fin 4) (Fin 4) ℝ => A i j) (hF hw)) k hz
  have chr (z : E4) (hz : z ∈ s) (i j k : Fin 4) :
      christoffel G' z i j k = christoffel G z i j k := by
    simp only [christoffel, invMetric, hG hz, dG z hz]
  have dChr (z : E4) (hz : z ∈ s) (i j k l : Fin 4) :
      coordPartial (fun w => christoffel G' w i j k) l z =
      coordPartial (fun w => christoffel G w i j k) l z :=
    partial_eq_on_open hs (fun w hw => chr w hw i j k) l hz
  have ric (i j : Fin 4) : ricci G' y i j = ricci G y i j := by
    simp only [ricci, riemann, dChr y hy, chr y hy]
  have flux (i j : Fin 4) :
      coordPartial (fun z => Real.sqrt |(G' z).det| * raiseBoth G' F' z i j) i y =
      coordPartial (fun z => Real.sqrt |(G z).det| * raiseBoth G F z i j) i y := by
    apply partial_eq_on_open hs _ i hy
    intro z hz
    simp only [raiseBoth, invMetric, hG hz, hF hz]
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    simpa only [einsteinTensor, scalarCurvature, maxwellSource, raiseBoth, invMetric,
      hG hy, hF hy, ric] using hem.1 i j
  · intro j
    simpa only [flux] using hem.2.1 j
  · intro i j k
    simpa only [dF y hy] using hem.2.2 i j k

theorem NoHair.isElectrovac_of_coordinate_equations (U : TopologicalSpace.Opens E4) (G F : E4 → Matrix (Fin 4) (Fin 4) ℝ)
    (h : ∀ y ∈ U, EinsteinMaxwellAt G F y) :
    IsElectrovac (M := U) (fun x => matrixBilin (G x.val)) (fun x => matrixBilin (F x.val)) := by
  intro c hc y hy
  obtain ⟨p, hp⟩ := TopologicalSpace.Opens.chart_eq (H := E4) ⟨c.symm y⟩ hc
  have hchart (x : U) : c = chartAt E4 x := hp.trans (by rfl)
  have hval (z : E4) (hz : z ∈ c.target) : (c.symm z).val = z := by
    have eqval (x : U) : c x = x.val := by rw [hchart x] <;> rfl
    exact (eqval (c.symm z)).symm.trans (c.right_inv hz)
  have derivAt (x : U) :
      (mfderiv 𝓘(ℝ, E4) 𝓘(ℝ, E4) c.symm x.val : E4 →L[ℝ] E4) = ContinuousLinearMap.id ℝ E4 := by
    rw [hchart x]
    have hd := mfderivWithin_range_extChartAt_symm (I := 𝓘(ℝ, E4)) (x := x)
    simp only [modelWithCornersSelf_coe, range_id, mfderivWithin_univ] at hd
    exact hd
  have coeff (A : E4 → Matrix (Fin 4) (Fin 4) ℝ) :
      EqOn (pullbackCoeffs (M := U) (fun x => matrixBilin (A x.val)) c.symm) A c.target := by
    intro z hz
    have hd := derivAt (c.symm z)
    rw [hval z hz] at hd
    funext i j
    unfold pullbackCoeffs
    rw [hd]
    change matrixBilin (A (c.symm z).val) (coordBasis i) (coordBasis j) = A z i j
    rw [hval z hz]
    change Matrix.toLinearMap₂' ℝ (A z) (WithLp.ofLp (coordBasis i))
      (WithLp.ofLp (coordBasis j)) = A z i j
    simp only [coordBasis, EuclideanSpace.single, PiLp.ofLp_single]
    rw [Matrix.toLinearMap₂'_apply]
    simp_rw [← Finset.smul_sum]
    simp [Pi.single_apply, ite_smul, Finset.sum_ite_eq, Finset.sum_ite_eq']
  apply einsteinMaxwell_of_eqOn c.open_target (coeff G) (coeff F) hy
  apply h
  rw [← hval y hy]
  exact (c.symm y).property
end


namespace ElectrovacProof005

open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Cartesian _root_.NoHair.TwoCentre.Model
open NoHair NoHair.TwoCentre NoHair.TwoCentre.Cartesian NoHair.TwoCentre.Model Set Topology Filter
open scoped ContDiff Manifold RealInnerProductSpace BigOperators

namespace NoHair.TwoCentre.Model.Continuation
open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Model

noncomputable section

private abbrev AM (f : E4 → ℝ) (z : E4) := ContDiffAt ℝ ω f z
private abbrev Mat4 := Matrix (Fin 4) (Fin 4) ℝ

theorem partial_an {f : E4 → ℝ} {z : E4} (hf : AM f z) (i : Fin 4) :
    AM (coordPartial f i) z :=
  (hf.fderiv_right (m := ω) (by simp)).clm_apply contDiffAt_const

theorem det_an {G : E4 → Mat4} {z : E4} (hG : ∀ i j, AM (fun x => G x i j) z) :
    AM (fun x => (G x).det) z := by
  simp only [Matrix.det_apply']
  unfold AM
  fun_prop

theorem inv_an {G : E4 → Mat4} {z : E4} (hG : ∀ i j, AM (fun x => G x i j) z)
    (hn : (G z).det ≠ 0) (i j : Fin 4) : AM (fun x => invMetric G x i j) z := by
  have ha : AM (fun x => ((G x).adjugate) i j) z := by
    simp_rw [Matrix.adjugate_apply]
    apply det_an
    intro a b
    by_cases h : a = j
    · subst a
      simp only [Matrix.updateRow_self]
      exact contDiffAt_const
    · simpa [Matrix.updateRow_ne h] using hG a b
  simpa [invMetric, Matrix.inv_def, Ring.inverse_eq_inv] using ((det_an hG).inv hn).mul ha

def einResidual (G F : E4 → Mat4) (i j : Fin 4) (x : E4) :=
  einsteinTensor G x i j - maxwellSource G F x i j
def divResidual (G F : E4 → Mat4) (j : Fin 4) (x : E4) :=
  ∑ i, coordPartial (fun y => Real.sqrt |(G y).det| * raiseBoth G F y i j) i x
def closedResidual (F : E4 → Mat4) (i j k : Fin 4) (x : E4) :=
  coordPartial (fun y => F y j k) i x + coordPartial (fun y => F y k i) j x +
    coordPartial (fun y => F y i j) k x

theorem residual_an {G F : E4 → Mat4} {z : E4}
    (hG : ∀ i j, AM (fun x => G x i j) z) (hF : ∀ i j, AM (fun x => F x i j) z)
    (hn : (G z).det ≠ 0) :
    (∀ i j, AM (einResidual G F i j) z) ∧ (∀ j, AM (divResidual G F j) z) ∧
    ∀ i j k, AM (closedResidual F i j k) z := by
  have hi := inv_an hG hn
  have hpart i j k := partial_an (hG i j) k
  have hc (i j k : Fin 4) : AM (fun x => christoffel G x i j k) z := by
    unfold AM christoffel
    fun_prop
  have hpc (i j k l : Fin 4) := partial_an (hc i j k) l
  have hr (i j : Fin 4) : AM (fun x => ricci G x i j) z := by
    unfold AM ricci riemann
    fun_prop
  have hu (i j : Fin 4) : AM (fun x => raiseBoth G F x i j) z := by
    unfold AM raiseBoth
    fun_prop
  have hsq : AM (fun x => Real.sqrt |(G x).det|) z :=
    by simpa only [Real.norm_eq_abs] using (((det_an hG).norm ℝ hn).sqrt (norm_ne_zero_iff.mpr hn))
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    unfold AM einResidual einsteinTensor scalarCurvature maxwellSource
    fun_prop
  · intro j
    have hd (i : Fin 4) := partial_an (hsq.mul (hu i j)) i
    unfold AM divResidual
    fun_prop
  · intro i j k
    exact ((partial_an (hF j k) i).add (partial_an (hF k i) j)).add (partial_an (hF i j) k)

theorem spatial_an : ContDiff ℝ ω spatial :=
  contDiff_euclidean.2 (fun i => contDiff_piLp_apply (p := 2) (i := i.succ))

theorem coordinates_an : ContDiff ℝ ω (fun p : ℝ × E3 => coordinates p.1 p.2) := by
  apply contDiff_euclidean.2
  intro i
  refine Fin.cases (by exact contDiff_fst) (fun j => ?_) i
  simp only [coordinates, WithLp.ofLp_toLp, Fin.cons_succ]
  fun_prop

theorem unit_dir (z : E4) (h : 0 < ‖spatial z‖) : ‖angularDirection z‖ = 1 := by
  rw [angularDirection, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr h), inv_mul_cancel₀ h.ne']

theorem collar_data {z : E4} (hc : |‖spatial z‖ - 1| < 1/4) :
    (∀ i j, AM (fun x => metricCoeffs x i j) z) ∧
    (∀ i j, AM (fun x => faradayCoeffs x i j) z) ∧
    Matrix.det (metricCoeffs z : Mat4) ≠ 0 := by
  have hp : 0 < ‖spatial z‖ := by linarith [(abs_lt.mp hc).1]
  have hu := unit_dir z hp
  have hd : |angularDirection z 0| ≤ 1 := by
    simpa [Real.norm_eq_abs, hu] using (PiLp.norm_apply_le (angularDirection z) 0)
  have hreg := Advanced.regular_horizon.1 (parameters z) hc hd
  have hnorm := spatial_an.contDiffAt.norm ℝ (norm_pos_iff.mp hp)
  have hdire : ContDiffAt ℝ ω angularDirection z :=
    (hnorm.inv hp.ne').smul spatial_an.contDiffAt
  have hparams : ContDiffAt ℝ ω parameters z :=
    (hnorm.sub contDiffAt_const).prodMk ((contDiffAt_piLp_apply (p := 2) (i := (0 : Fin 3))).comp z hdire)
  have hfn (f : ℝ × ℝ → ℝ) (hf : f ∈ [Advanced.gvv, Advanced.gvr, Advanced.grr, Advanced.angularScale,
        Advanced.potentialV, Advanced.potentialR]) : AM (fun x => f (parameters x)) z :=
    (hreg.2.1 f hf).contDiffAt.comp z hparams
  have hvv := hfn _ (by simp : Advanced.gvv ∈ _)
  have hvr := hfn _ (by simp : Advanced.gvr ∈ _)
  have hrr := hfn _ (by simp : Advanced.grr ∈ _)
  have ha := hfn _ (by simp : Advanced.angularScale ∈ _)
  have hv := hfn _ (by simp : Advanced.potentialV ∈ _)
  have hav := hfn _ (by simp : Advanced.potentialR ∈ _)
  have hdr (i : Fin 4) : AM (fun x => dr x i) z := by
    refine Fin.cases (by exact contDiffAt_const) (fun j => ?_) i
    exact (contDiffAt_piLp_apply (p := 2) (i := j)).comp z hdire
  have hpotential (i : Fin 4) : AM (potential i) z :=
    (hv.mul contDiffAt_const).add (hav.mul (hdr i))
  refine ⟨?_, fun i j => (partial_an (hpotential j) i).sub (partial_an (hpotential i) j), ?_⟩
  · intro i j
    exact (((hvv.mul contDiffAt_const).mul contDiffAt_const).add
      (hvr.mul ((contDiffAt_const.mul (hdr j)).add ((hdr i).mul contDiffAt_const))) |>.add
      ((hrr.mul (hdr i)).mul (hdr j))).add
      ((ha.div (hnorm.pow 2) (pow_ne_zero 2 hp.ne')).mul (contDiffAt_const.sub ((hdr i).mul (hdr j))))
  · let n := angularDirection z
    let a := Advanced.gvv (parameters z)
    let b := Advanced.gvr (parameters z)
    let d := Advanced.grr (parameters z)
    let k := Advanced.angularScale (parameters z) / ‖spatial z‖ ^ 2
    have hk : 0 < k := div_pos (sq_pos_of_pos hreg.1) (sq_pos_of_pos hp)
    have hrad : a * d - b ^ 2 = -1 := hreg.2.2.1
    have hs : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1 := by
      have h : ‖n‖ ^ 2 = 1 := by rw [show ‖n‖ = 1 from hu]; norm_num
      simpa [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three] using h
    let B : Mat4 := !![a, b*n 0, b*n 1, b*n 2;
      b*n 0, k+(d-k)*n 0*n 0, (d-k)*n 0*n 1, (d-k)*n 0*n 2;
      b*n 1, (d-k)*n 1*n 0, k+(d-k)*n 1*n 1, (d-k)*n 1*n 2;
      b*n 2, (d-k)*n 2*n 0, (d-k)*n 2*n 1, k+(d-k)*n 2*n 2]
    have hB : (metricCoeffs z : Mat4) = B := by
      have dr0 : dr z 0 = 0 := rfl
      have dr1 : dr z 1 = n 0 := rfl
      have dr2 : dr z 2 = n 1 := rfl
      have dr3 : dr z 3 = n 2 := rfl
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp (config := {decide := true}) [metricCoeffs, dt, dr0, dr1, dr2, dr3, spatialDelta, a, b, d, k, B] <;> ring
    have hdet : B.det = k^2 * (a*d-b^2) := by
      rw [Matrix.det_succ_row_zero]
      simp [Fin.sum_univ_four, Matrix.det_fin_three, Matrix.submatrix_apply, B, Fin.succAbove]
      linear_combination k ^ 2 * (a * (d-k)-b^2) * hs
    rw [hB, hdet, hrad]
    positivity

theorem extend_scalar (f : E4 → ℝ)
    (han : ∀ z, |‖spatial z‖ - 1| < 1/4 → AM f z)
    (hzero : ∀ z ∈ outerRegion, f z = 0) {z : E4} (hz : z ∈ manifold) : f z = 0 := by
  change 3 / 4 < ‖spatial z‖ ∧ spatial z ≠ (3 : ℝ) • unitAxis at hz
  by_cases ho : 1 < ‖spatial z‖
  · exact hzero z ⟨ho, hz.2⟩
  let r := ‖spatial z‖ - 1
  let n := angularDirection z
  have hp : 0 < ‖spatial z‖ := by linarith [hz.1]
  have hn : ‖n‖ = 1 := unit_dir z hp
  let ray := fun s : ℝ => coordinates (z 0) ((1+s) • n)
  have hray : ContDiff ℝ ω ray :=
    coordinates_an.comp (contDiff_const.prodMk ((contDiff_const.add contDiff_id).smul contDiff_const))
  have hnray {s : ℝ} (hs : -(1/4 : ℝ) < s) : ‖spatial (ray s)‖ = 1+s := by
    change ‖spatial (coordinates _ _)‖ = _
    rw [Model.spatial_coordinates, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith), hn, mul_one]
  have har : AnalyticOnNhd ℝ (fun s => f (ray s)) (Ioo (-(1/4 : ℝ)) (1/4)) := by
    intro s hs
    exact ((han (ray s) (by rw [hnray hs.1]; apply abs_lt.mpr; constructor <;> linarith [hs.1, hs.2])).comp
      s hray.contDiffAt).analyticAt
  have hpos {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) (1/4)) : ray s ∈ outerRegion := by
    have hn' := hnray (s := s) (by linarith [hs.1])
    refine ⟨by linarith [hs.1], ?_⟩
    intro heq
    have h3 : ‖spatial (ray s)‖ = 3 := by rw [heq, norm_smul]; norm_num [unitAxis]
    linarith [hs.2]
  have hev : (fun s => f (ray s)) =ᶠ[𝓝 (1/8 : ℝ)] 0 := by
    filter_upwards [Ioo_mem_nhds (a := (0 : ℝ)) (b := 1/4) (by norm_num : 0 < (1/8 : ℝ)) (by norm_num)] with s hs
    exact hzero _ (hpos hs)
  have hall := har.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_Ioo
    (show (1/8 : ℝ) ∈ Ioo (- (1/4 : ℝ)) (1/4) by constructor <;> norm_num) hev
  have hr : r ∈ Ioo (-(1/4 : ℝ)) (1/4) := by dsimp [r]; constructor <;> linarith [hz.1]
  have hid : ray r = z := by
    change coordinates (z 0) ((1 + (‖spatial z‖ - 1)) • (‖spatial z‖⁻¹ • spatial z)) = z
    rw [show 1 + (‖spatial z‖ - 1) = ‖spatial z‖ by ring, smul_smul,
      mul_inv_cancel₀ hp.ne', one_smul]
    ext i
    exact Fin.cases rfl (fun j => by rfl) i
  simpa only [hid, Pi.zero_apply] using hall hr

theorem across (he : ∀ z ∈ outerRegion, EinsteinMaxwellAt metricCoeffs faradayCoeffs z) :
    IsElectrovac metric faraday := by
  apply isElectrovac_of_coordinate_equations manifold metricCoeffs faradayCoeffs
  intro z hz
  have ha (x : E4) (hx : |‖spatial x‖ - 1| < 1/4) := by
    obtain ⟨hG, hF, hd⟩ := collar_data hx
    exact residual_an (G := metricCoeffs) (F := faradayCoeffs) hG hF hd
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    apply sub_eq_zero.mp
    exact extend_scalar (einResidual metricCoeffs faradayCoeffs i j)
      (fun x hx => (ha x hx).1 i j) (fun x hx => sub_eq_zero.mpr ((he x hx).1 i j)) hz
  · intro j
    exact extend_scalar (divResidual metricCoeffs faradayCoeffs j)
      (fun x hx => (ha x hx).2.1 j) (fun x hx => (he x hx).2.1 j) hz
  · intro i j k
    exact extend_scalar (closedResidual faradayCoeffs i j k)
      (fun x hx => (ha x hx).2.2 i j k) (fun x hx => (he x hx).2.2 i j k) hz

end
end NoHair.TwoCentre.Model.Continuation

open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Model
open NoHair.TwoCentre.Model.Continuation

theorem checkedResult (he : ∀ z ∈ outerRegion, EinsteinMaxwellAt metricCoeffs faradayCoeffs z) :
    IsElectrovac metric faraday := across he
end ElectrovacProof005

alias NoHair.TwoCentre.Model.electrovac_across_horizon := ElectrovacProof005.checkedResult


















section

noncomputable section
open scoped Matrix.Norms.Elementwise
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem FunctionalInequalities.Analysis.fderiv_det_eq_sum_updateRow (M N : Matrix ι ι ℝ) :
    fderiv ℝ Matrix.det M N = ∑ i, (M.updateRow i (N i)).det := by
  change fderiv ℝ (FunctionalInequalities.Analysis.detML : (ι → ι → ℝ) → ℝ) (fun i => M i) (fun i => N i) = _
  rw [(FunctionalInequalities.Analysis.detML.hasFDerivAt (fun i => M i)).fderiv, ContinuousMultilinearMap.linearDeriv_apply]
  apply Finset.sum_congr rfl
  intro i _hi
  rfl

theorem FunctionalInequalities.Analysis.fderiv_det_eq_det_mul_trace_readable (M N : Matrix ι ι ℝ) (hM : IsUnit M.det) :
    fderiv ℝ Matrix.det M N = M.det * Matrix.trace (M⁻¹ * N) := by
  have hNM : (N * M⁻¹) * M = N := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul M hM, Matrix.mul_one]
  have hrow (i : ι) : N i = ∑ j, (N * M⁻¹) i j • M j := by
    calc
      N i = ((N * M⁻¹) * M) i := congrArg (fun Q : Matrix ι ι ℝ => Q i) hNM.symm
      _ = _ := by
        ext k
        simp only [Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [FunctionalInequalities.Analysis.fderiv_det_eq_sum_updateRow]
  calc
    (∑ i, (M.updateRow i (N i)).det) = ∑ i, (N * M⁻¹) i i * M.det := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [hrow, Matrix.det_updateRow_sum]
      rfl
    _ = Matrix.trace (N * M⁻¹) * M.det := by
      rw [Matrix.trace, Finset.sum_mul]
      rfl
    _ = M.det * Matrix.trace (M⁻¹ * N) := by
      rw [Matrix.trace_mul_comm]
      ring
end
end




namespace ElectrovacProof025

open _root_.NoHair
open NoHair Set Filter Topology
open scoped ContDiff BigOperators Matrix.Norms.Elementwise

namespace NoHair.AtlasBridge
open _root_.NoHair
noncomputable section
abbrev Pt := ExactVacuumAtlas.Pt 4
abbrev M4 := Matrix (Fin 4) (Fin 4) ℝ
abbrev SC (f : E4 → ℝ) (y : E4) := ContDiffAt ℝ ∞ f y
abbrev EMetric := E4 → M4
abbrev enc (G : EMetric) : ExactVacuumAtlas.Metric 4 := fun i j x => G (WithLp.toLp 2 x) i j
abbrev encodeSet (S : Set E4) := (WithLp.toLp 2 : Pt → E4) ⁻¹' S

def pack : Pt →L[ℝ] E4 := LinearMap.toContinuousLinearMap (WithLp.linearEquiv 2 ℝ Pt).symm.toLinearMap
def unpack : E4 →L[ℝ] Pt := LinearMap.toContinuousLinearMap (WithLp.linearEquiv 2 ℝ Pt).toLinearMap

theorem coord_slice (p : Pt) (i : Fin 4) :
    HasDerivAt (fun s : ℝ => WithLp.toLp 2 (Function.update p i s) : ℝ → E4) (coordBasis i) (p i) := by
  have eq : (fun s : ℝ => WithLp.toLp 2 (Function.update p i s) : ℝ → E4) =
      (fun s : ℝ => WithLp.toLp 2 p + (s-p i) • coordBasis i) := by
    funext s; ext j
    by_cases hj : j=i
    · subst j;simp [coordBasis,PiLp.add_apply,PiLp.smul_apply]
    · simp [coordBasis,Function.update_of_ne hj,PiLp.add_apply,PiLp.smul_apply,Pi.single_apply,hj,Ne.symm hj]
  rw [eq]
  simpa using (((hasDerivAt_id (p i)).sub_const (p i)).smul_const (coordBasis i)).const_add (WithLp.toLp 2 p)

theorem pd_eq {f : E4 → ℝ} {p : Pt} (hf : DifferentiableAt ℝ f (WithLp.toLp 2 p)) (i : Fin 4) :
    ExactVacuumAtlas.pd i (fun x : Pt => f (WithLp.toLp 2 x)) p = coordPartial f i (WithLp.toLp 2 p) := by
  have hd : HasFDerivAt f (fderiv ℝ f (WithLp.toLp 2 p)) (WithLp.toLp 2 (Function.update p i (p i))) := by simpa using hf.hasFDerivAt
  exact (hd.comp_hasDerivAt (p i) (coord_slice p i)).deriv

theorem partial_smooth {f : E4 → ℝ} {z : E4} (hf : SC f z) (i : Fin 4) : SC (coordPartial f i) z :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const

theorem det_smooth {G : EMetric} {y : E4} (hG : ∀ i j, SC (fun x => G x i j) y) :
    SC (fun x => (G x).det) y := by simp only [Matrix.det_apply'];unfold SC;fun_prop

theorem inv_smooth {G : EMetric} {y : E4} (hG : ∀ i j, SC (fun x => G x i j) y)
    (hn : (G y).det ≠ 0) (i j : Fin 4) : SC (fun x => invMetric G x i j) y := by
  have ha : SC (fun x => ((G x).adjugate) i j) y := by
    simp_rw [Matrix.adjugate_apply]
    apply det_smooth
    intro a b
    by_cases h : a = j
    · subst a;simp only [Matrix.updateRow_self];exact contDiffAt_const
    · simpa [Matrix.updateRow_ne h] using hG a b
  simpa [invMetric, Matrix.inv_def, Ring.inverse_eq_inv] using ((det_smooth hG).inv hn).mul ha

theorem chr_smooth {G : EMetric} {y : E4} (hG : ∀ i j, SC (fun x => G x i j) y)
    (hn : (G y).det ≠ 0) (i j k : Fin 4) : SC (fun x => christoffel G x i j k) y := by
  have hi := inv_smooth hG hn
  have hpart (a b c : Fin 4) := partial_smooth (hG a b) c
  unfold SC christoffel;fun_prop

theorem upper_smooth {G F : EMetric} {y : E4} (hG : ∀ i j, SC (fun x => G x i j) y)
    (hF : ∀ i j, SC (fun x => F x i j) y) (hn : (G y).det ≠ 0) (i j : Fin 4) :
    SC (fun x => raiseBoth G F x i j) y := by
  have hi := inv_smooth hG hn
  unfold SC raiseBoth;fun_prop

theorem chr_bridge {G : EMetric} {p : Pt}
    (hG : ∀ i j, SC (fun x => G x i j) (WithLp.toLp 2 p)) (a b c : Fin 4) :
    ExactVacuumAtlas.christoffel (enc G) (enc (invMetric G)) a b c p =
      christoffel G (WithLp.toLp 2 p) a b c := by
  have hd (i j k : Fin 4) := pd_eq ((hG i j).differentiableAt (by simp)) k
  simp only [ExactVacuumAtlas.christoffel,enc,hd,christoffel,Finset.sum_div]
  apply Finset.sum_congr rfl; intro k _;ring

theorem chr_symm {G : EMetric} {S : Set E4} (hS : IsOpen S)
    (hG : ∀ x ∈ S, (G x).transpose=G x) {y : E4} (hy : y ∈ S) (a b c : Fin 4) :
    christoffel G y a b c = christoffel G y a c b := by
  have ev : (fun x => G x b c) =ᶠ[𝓝 y] (fun x => G x c b) :=
    Filter.mem_of_superset (hS.mem_nhds hy) (fun x hx => congrFun (congrFun (hG x hx) c) b)
  have hder (k : Fin 4) : coordPartial (fun x => G x b c) k y = coordPartial (fun x => G x c b) k y :=
    DFunLike.congr_fun ev.fderiv_eq _
  unfold christoffel
  simp only [hder]
  apply Finset.sum_congr rfl;intro k _;ring

theorem ricci_bridge {G : EMetric} {S : Set E4} (hS : IsOpen S)
    (hsm : ∀ x ∈ S, ∀ i j, SC (fun w => G w i j) x)
    (hsym : ∀ x ∈ S, (G x).transpose=G x) {p : Pt} (hp : WithLp.toLp 2 p ∈ S)
    (hn : (G (WithLp.toLp 2 p)).det ≠ 0) (i j : Fin 4) :
    ExactVacuumAtlas.ricciOf (enc G) (enc (invMetric G)) i j p = ricci G (WithLp.toLp 2 p) i j := by
  let y := WithLp.toLp 2 p
  have hder (a b c k : Fin 4) : ExactVacuumAtlas.pd k (ExactVacuumAtlas.christoffel (enc G) (enc (invMetric G)) a b c) p =
      coordPartial (fun x => christoffel G x a c b) k y := by
    let f := fun x => christoffel G x a c b
    have hd : HasDerivAt (fun t : ℝ => WithLp.toLp 2 (Function.update p k t) : ℝ → E4) (coordBasis k) (p k) := coord_slice p k
    have h0 : WithLp.toLp 2 (Function.update p k (p k)) ∈ S := by simpa using hp
    have he : (fun t => ExactVacuumAtlas.christoffel (enc G) (enc (invMetric G)) a b c (Function.update p k t)) =ᶠ[𝓝 (p k)]
        (fun t => f (WithLp.toLp 2 (Function.update p k t))) := by
      filter_upwards [hd.continuousAt (hS.mem_nhds h0)] with t ht
      exact (chr_bridge (hsm _ ht) a b c).trans (chr_symm hS hsym ht _ _ _)
    exact he.deriv_eq.trans (pd_eq ((chr_smooth (hsm _ hp) hn a c b).differentiableAt (by simp)) k)
  have hchr := chr_bridge (hsm _ hp)
  unfold ExactVacuumAtlas.ricciOf ExactVacuumAtlas.ricci ricci riemann
  simp only [hder,hchr]
  apply Finset.sum_congr rfl; intro k _
  congr 1
  apply Finset.sum_congr rfl;intro l _
  rw [chr_symm hS hsym hp l i j,chr_symm hS hsym hp l i k]

theorem ein_bridge {G F : EMetric} {S : Set E4} (hS : IsOpen S)
    (hsm : ∀ x ∈ S, ∀ i j, SC (fun w => G w i j) x) (hsym : ∀ x ∈ S, (G x).transpose=G x)
    {p : Pt} (hp : WithLp.toLp 2 p ∈ S) (hn : (G (WithLp.toLp 2 p)).det ≠ 0) (i j : Fin 4) :
    ExactVacuumAtlas.EinsteinMaxwell.einsteinMaxwell (enc G) (enc (invMetric G)) (enc F) i j p =
      einsteinTensor G (WithLp.toLp 2 p) i j - maxwellSource G F (WithLp.toLp 2 p) i j := by
  have hr := ricci_bridge hS hsm hsym hp hn
  unfold ExactVacuumAtlas.EinsteinMaxwell.einsteinMaxwell ExactVacuumAtlas.EinsteinMaxwell.ricciScalar
    ExactVacuumAtlas.EinsteinMaxwell.emStress ExactVacuumAtlas.EinsteinMaxwell.fieldSq
    ExactVacuumAtlas.EinsteinMaxwell.raise2 einsteinTensor scalarCurvature maxwellSource raiseBoth
  simp only [hr,enc]
  ring

def derivMatrix (G : EMetric) (k : Fin 4) (y : E4) : M4 := fun a b => coordPartial (fun x => G x a b) k y

theorem det_partial {G : EMetric} {y : E4} (hG : ∀ a b, SC (fun w => G w a b) y)
    (hn : (G y).det≠0) (k : Fin 4) :
    coordPartial (fun x => (G x).det) k y = (G y).det * Matrix.trace ((G y)⁻¹ * derivMatrix G k y) := by
  have hmat : DifferentiableAt ℝ G y := by
    apply differentiableAt_pi.mpr;intro i
    apply differentiableAt_pi.mpr;intro j
    exact (hG i j).differentiableAt (by simp)
  have hdet : DifferentiableAt ℝ (Matrix.det : M4 → ℝ) (G y) := by
    exact ((FunctionalInequalities.Analysis.detML (ι := Fin 4)).hasFDerivAt (G y)).differentiableAt
  have hd : fderiv ℝ G y (coordBasis k) = derivMatrix G k y := by
    ext i j
    let P₁ : M4 →L[ℝ] (Fin 4 → ℝ) := (ContinuousLinearMap.proj (φ := fun _ : Fin 4 => Fin 4 → ℝ) i)
    let P₂ : (Fin 4 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj (φ := fun _ : Fin 4 => ℝ) j
    let P := P₂.comp P₁
    exact (DFunLike.congr_fun (P.hasFDerivAt.comp y hmat.hasFDerivAt).fderiv (coordBasis k)).symm
  have h := DFunLike.congr_fun (hdet.hasFDerivAt.comp y hmat.hasFDerivAt).fderiv (coordBasis k)
  exact h.trans ((FunctionalInequalities.Analysis.fderiv_det_eq_det_mul_trace_readable
    (G y) (fderiv ℝ G y (coordBasis k)) (isUnit_iff_ne_zero.mpr hn)).trans (by rw [hd]))

theorem trace_christoffel {G : EMetric} {y : E4} (hsym : (G y).transpose=G y) (k : Fin 4) :
    ∑ a, christoffel G y a a k = Matrix.trace ((G y)⁻¹ * derivMatrix G k y) / 2 := by
  have hisym : (invMetric G y).transpose=invMetric G y := by
    unfold invMetric;rw [Matrix.transpose_nonsing_inv,hsym]
  have hi (a b : Fin 4) : invMetric G y a b = invMetric G y b a := congrFun (congrFun hisym b) a
  have cancel : (∑ a, ∑ l, invMetric G y a l * coordPartial (fun x => G x l k) a y) =
      ∑ a, ∑ l, invMetric G y a l * coordPartial (fun x => G x a k) l y := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl;intro a _;apply Finset.sum_congr rfl;intro l _;rw [hi l a]
  unfold christoffel Matrix.trace
  simp only [Matrix.diag_apply, Matrix.mul_apply, derivMatrix]
  have e (a l : Fin 4) : 1/2 * invMetric G y a l *
      (coordPartial (fun x => G x l k) a y+coordPartial (fun x => G x l a) k y-coordPartial (fun x => G x a k) l y) =
      (invMetric G y a l * coordPartial (fun x => G x l k) a y + invMetric G y a l * coordPartial (fun x => G x l a) k y -
       invMetric G y a l * coordPartial (fun x => G x a k) l y)/2 := by ring
  change (∑ a : Fin 4, ∑ l : Fin 4, (1/2:ℝ) * invMetric G y a l * _) = _
  simp_rw [e]
  simp only [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_add_distrib,cancel]
  dsimp [invMetric]
  ring

def volume (G : EMetric) (y : E4) := Real.sqrt |(G y).det|

theorem volume_partial {G : EMetric} {y : E4} (hG : ∀ i j, SC (fun x => G x i j) y)
    (hn : (G y).det≠0) (hsym : (G y).transpose=G y) (k : Fin 4) :
    coordPartial (volume G) k y = volume G y * ∑ a, christoffel G y a a k := by
  have hd := (det_smooth hG).differentiableAt (by simp)
  have hpos : 0<volume G y := Real.sqrt_pos.mpr (abs_pos.mpr hn)
  have hsq : volume G y ^ 2 = |(G y).det| := Real.sq_sqrt (abs_nonneg _)
  rw [trace_christoffel hsym]
  rcases lt_or_gt_of_ne hn with hN | hP
  · have ev : volume G =ᶠ[𝓝 y] (fun x => Real.sqrt (-(G x).det)) := by
      filter_upwards [hd.continuousAt.eventually_lt_const hN] with x hx
      simp [volume,abs_of_neg hx]
    have hf := (hd.hasFDerivAt.neg).sqrt (neg_ne_zero.mpr hn)
    have e := DFunLike.congr_fun (ev.fderiv_eq.trans hf.fderiv) (coordBasis k)
    change fderiv ℝ (volume G) y (coordBasis k) = _
    rw [e]
    rw [abs_of_neg hN] at hsq
    change (1 / (2 * Real.sqrt (-(G y).det))) * -(coordPartial (fun x => (G x).det) k y) = _
    have hv : Real.sqrt (-(G y).det) = volume G y := by simp [volume,abs_of_neg hN]
    rw [hv,det_partial hG hn]
    field_simp [hpos.ne']
    <;> nlinarith [congrArg (· * Matrix.trace ((G y)⁻¹ * derivMatrix G k y)) hsq]
  · have ev : volume G =ᶠ[𝓝 y] (fun x => Real.sqrt (G x).det) := by
      filter_upwards [hd.continuousAt.eventually_const_lt hP] with x hx
      simp [volume,abs_of_pos hx]
    have hf := hd.hasFDerivAt.sqrt hn
    have e := DFunLike.congr_fun (ev.fderiv_eq.trans hf.fderiv) (coordBasis k)
    change fderiv ℝ (volume G) y (coordBasis k) = _
    rw [e]
    rw [abs_of_pos hP] at hsq
    change (1 / (2 * Real.sqrt (G y).det)) * coordPartial (fun x => (G x).det) k y = _
    have hv : Real.sqrt (G y).det = volume G y := by simp [volume,abs_of_pos hP]
    rw [hv,det_partial hG hn]
    field_simp [hpos.ne']
    <;> nlinarith [congrArg (· * Matrix.trace ((G y)⁻¹ * derivMatrix G k y)) hsq]

theorem raised_anti {G F : EMetric} {y : E4} (hF : ∀ i j, F y i j = - F y j i) (i j : Fin 4) :
    raiseBoth G F y i j = -raiseBoth G F y j i := by
  unfold raiseBoth
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl;intro l _
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl;intro k _
  rw [hF k l]
  ring

def divDensity (G F : EMetric) (j : Fin 4) (y : E4) :=
  ∑ i, coordPartial (fun x => volume G x * raiseBoth G F x i j) i y

theorem div_bridge {G F : EMetric} {S : Set E4} (hS : IsOpen S)
    (hsym : ∀ x ∈ S, (G x).transpose=G x) {p : Pt} (hp : WithLp.toLp 2 p ∈ S)
    (hG : ∀ i j, SC (fun x => G x i j) (WithLp.toLp 2 p)) (hF : ∀ i j, SC (fun x => F x i j) (WithLp.toLp 2 p))
    (hn : (G (WithLp.toLp 2 p)).det ≠ 0) (ha : ∀ i j, F (WithLp.toLp 2 p) i j = -F (WithLp.toLp 2 p) j i) (b : Fin 4) :
    divDensity G F b (WithLp.toLp 2 p) = volume G (WithLp.toLp 2 p) *
      ExactVacuumAtlas.EinsteinMaxwell.maxwellDiv (enc G) (enc (invMetric G)) (enc F) b p := by
  let y : E4 := WithLp.toLp 2 p
  let A (i j : Fin 4) := raiseBoth G F y i j
  let C (i j k : Fin 4) := christoffel G y i j k
  have hpd (i : Fin 4) :
      ExactVacuumAtlas.pd i (ExactVacuumAtlas.EinsteinMaxwell.raise2 (enc (invMetric G)) (enc F) i b) p =
      coordPartial (fun x => raiseBoth G F x i b) i y :=
    pd_eq ((upper_smooth hG hF hn i b).differentiableAt (by simp)) i
  have hv : SC (volume G) y := ((det_smooth hG).norm ℝ hn).sqrt (norm_ne_zero_iff.mpr hn)
  have hdiff (i : Fin 4) : coordPartial (fun x => volume G x * raiseBoth G F x i b) i y =
      volume G y * ((∑ a, C a a i)*A i b + coordPartial (fun x => raiseBoth G F x i b) i y) := by
    have hp := (hv.differentiableAt (by simp)).hasFDerivAt.mul ((upper_smooth hG hF hn i b).differentiableAt (by simp)).hasFDerivAt
    calc
      _ = volume G y * coordPartial (fun x => raiseBoth G F x i b) i y + A i b * coordPartial (volume G) i y := by
        simpa only [coordPartial,A,y,Pi.mul_def,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
          using DFunLike.congr_fun hp.fderiv (coordBasis i)
      _ = _ := by rw [volume_partial hG hn (hsym _ ‹_ ∈ S›)];dsimp [C];ring
  have vanish : (∑ i, ∑ k, C b i k * A i k) = 0 := by
    have h : (∑ i, ∑ k, C b i k * A i k) = -(∑ i, ∑ k, C b i k * A i k) := by
      calc
        _ = ∑ k, ∑ i, C b i k * A i k := Finset.sum_comm
        _ = _ := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl;intro k _;rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl;intro i _
          change christoffel G y b i k * raiseBoth G F y i k = -(christoffel G y b k i * raiseBoth G F y k i)
          calc
            _ = christoffel G y b k i * (-raiseBoth G F y k i) := congrArg₂ (· * ·) (chr_symm hS hsym hp b i k) (raised_anti ha i k)
            _ = _ := by ring
    linarith
  have reorder : (∑ i, (∑ a, C a a i)*A i b) = ∑ a, ∑ i, C a a i*A i b := by
    simp only [Finset.sum_mul];rw [Finset.sum_comm]
  change (∑ i, coordPartial (fun x => volume G x * raiseBoth G F x i b) i y) = _
  simp only [hdiff,← Finset.mul_sum,ExactVacuumAtlas.EinsteinMaxwell.maxwellDiv,hpd,chr_bridge hG]
  change volume G y * (∑ i, ((∑ a, C a a i)*A i b + coordPartial (fun x => raiseBoth G F x i b) i y)) =
    volume G y * (∑ a, (coordPartial (fun x => raiseBoth G F x a b) a y +
      ∑ k, (C a a k * A k b + C b a k * A a k)))
  simp only [Finset.sum_add_distrib,vanish,add_zero,zero_add,reorder,add_comm]

theorem cyclic_bridge {F : EMetric} {p : Pt} (hs : ∀ i j, SC (fun y => F y i j) (WithLp.toLp 2 p)) (a b c : Fin 4) :
    ExactVacuumAtlas.EinsteinMaxwell.faradayCyclic (enc F) a b c p =
      coordPartial (fun y => F y b c) a (WithLp.toLp 2 p) + coordPartial (fun y => F y c a) b (WithLp.toLp 2 p) +
        coordPartial (fun y => F y a b) c (WithLp.toLp 2 p) := by
  unfold ExactVacuumAtlas.EinsteinMaxwell.faradayCyclic enc
  rw [pd_eq ((hs b c).differentiableAt (by simp)), pd_eq ((hs c a).differentiableAt (by simp)), pd_eq ((hs a b).differentiableAt (by simp))]
end
end NoHair.AtlasBridge

open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Cartesian _root_.NoHair.TwoCentre.Model
open NoHair NoHair.TwoCentre NoHair.TwoCentre.Cartesian NoHair.TwoCentre.Model Set Topology
open scoped ContDiff Manifold RealInnerProductSpace

namespace NoHair.TwoCentre.Model.Curves
open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Model

noncomputable section

export _root_.ElectrovacProof003.NoHair.TwoCentre.Model.Curves (radialSpeed)

export _root_.ElectrovacProof003.NoHair.TwoCentre.Model.Curves (spatial_inner)

export _root_.ElectrovacProof003.NoHair.TwoCentre.Model.Curves (radialSpeed_coords)

export _root_.ElectrovacProof003.NoHair.TwoCentre.Model.Curves (metric_eval)

export _root_.ElectrovacProof003.NoHair.TwoCentre.Model.Curves (angular_unit)

end
end NoHair.TwoCentre.Model.Curves

namespace NoHair.TwoCentre.Advanced
open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Advanced
noncomputable section
export _root_.ElectrovacProof001.NoHair.TwoCentre.Advanced (gap_factor)

export _root_.ElectrovacProof001.NoHair.TwoCentre.Advanced (coefficient_analytic)

export _root_.ElectrovacProof001.NoHair.TwoCentre.Advanced (determinant)

export _root_.ElectrovacProof001.NoHair.TwoCentre.Advanced (match_exterior)

end
end NoHair.TwoCentre.Advanced

open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Cartesian _root_.NoHair.TwoCentre.Model
open NoHair NoHair.TwoCentre NoHair.TwoCentre.Cartesian NoHair.TwoCentre.Model Set Filter Topology
open scoped Manifold ContDiff RealInnerProductSpace BigOperators
namespace NoHair.TwoCentre.Model.Geo
open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Model
noncomputable section

export _root_.ElectrovacProof003.NoHair.TwoCentre.Model.Geo (Mat4)

export _root_.ElectrovacProof003.NoHair.TwoCentre.Model.Geo (AM)

export _root_.ElectrovacProof003.NoHair.TwoCentre.Model.Geo (spatial_an)

export _root_.ElectrovacProof003.NoHair.TwoCentre.Model.Geo (coordinate_an)

export _root_.ElectrovacProof003.NoHair.TwoCentre.Model.Geo (coords_self)

export _root_.ElectrovacProof003.NoHair.TwoCentre.Model.Geo (partial_an)

export _root_.ElectrovacProof003.NoHair.TwoCentre.Model.Geo (unit_inner)

export _root_.ElectrovacProof003.NoHair.TwoCentre.Model.Geo (param_norm)

export _root_.ElectrovacProof003.NoHair.TwoCentre.Model.Geo (radius_data)

export _root_.ElectrovacProof003.NoHair.TwoCentre.Model.Geo (reg_data)

end
end NoHair.TwoCentre.Model.Geo
open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Cartesian _root_.NoHair.TwoCentre.Model
open NoHair NoHair.TwoCentre NoHair.TwoCentre.Cartesian NoHair.TwoCentre.Model Set Filter Topology
open scoped Manifold ContDiff RealInnerProductSpace BigOperators
namespace NoHair.TwoCentre.Model.Geo
open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Model
noncomputable section

export _root_.ElectrovacProof003.NoHair.TwoCentre.Model.Geo (val_diff)

export _root_.ElectrovacProof003.NoHair.TwoCentre.Model.Geo (outer_open)

export _root_.ElectrovacProof003.NoHair.TwoCentre.Model.Geo (exterior_open)

export _root_.ElectrovacProof003.NoHair.TwoCentre.Model.Geo (adv_mem)

export _root_.ElectrovacProof003.NoHair.TwoCentre.Model.Geo (chart_coe)

set_option backward.isDefEq.respectTransparency false in
theorem chart_der {y : E4} (hy : y ∈ exterior) :
    (mfderiv 𝓘(ℝ,E4) 𝓘(ℝ,E4) Model.chart y : E4 →L[ℝ] E4) = fderiv ℝ toAdvanced y := by
  have he : (Subtype.val ∘ Model.chart : E4 → E4) =ᶠ[𝓝 y] toAdvanced :=
    Filter.mem_of_superset (exterior_open.mem_nhds hy) (fun _ h => chart_coe h)
  have cont := (ContMDiffAt.subtypeVal_comp_iff manifold Model.chart y).mp
    (((Cartesian.exterior_and_frontier.2.1.choose_spec.2.2.2.2.1 y hy).contMDiffAt (exterior_open.mem_nhds hy)).congr_of_eventuallyEq he)
  have hd := (val_diff (Model.chart y)).comp y (cont.mdifferentiableAt (by simp)).hasMFDerivAt
  have hh := (hasMFDerivAt_iff_hasFDerivAt.mp hd).fderiv
  exact hh.symm.trans he.fderiv_eq


end
end NoHair.TwoCentre.Model.Geo

open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Model _root_.NoHair.TwoCentre.Cartesian
open NoHair NoHair.TwoCentre NoHair.TwoCentre.Model NoHair.TwoCentre.Cartesian NoHair.AtlasBridge
open Set Filter Topology
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise
namespace NoHair.TwoCentre.Model.Transport
open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Model
noncomputable section

def mg (z : E4) : M4 := Matrix.of (metricCoeffs z)
def ff (z : E4) : M4 := Matrix.of (faradayCoeffs z)

def basis := (EuclideanSpace.basisFun (Fin 4) ℝ).toBasis
def jac (L : E4 →L[ℝ] E4) := LinearMap.toMatrix basis basis L.toLinearMap

theorem jac_apply (L : E4 →L[ℝ] E4) (a i : Fin 4) : jac L a i = L (coordBasis i) a := by
  simp [jac,LinearMap.toMatrix_apply,basis,coordBasis]

theorem jac_pair (L : E4 →L[ℝ] E4) (A : M4) (i j : Fin 4) :
    matrixBilin A (L (coordBasis i)) (L (coordBasis j)) = ((jac L).transpose * A * jac L) i j := by
  change Matrix.toLinearMap₂' ℝ A (WithLp.ofLp (L (coordBasis i))) (WithLp.ofLp (L (coordBasis j))) = _
  rw [Matrix.toLinearMap₂'_apply]
  simp only [Matrix.mul_apply,Matrix.transpose_apply,jac_apply,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl;intro a _;apply Finset.sum_congr rfl;intro b _;ring

theorem jac_comp {f g : E4 → E4} {x : E4} (hf : DifferentiableAt ℝ f (g x))
    (hg : DifferentiableAt ℝ g x) (he : f ∘ g =ᶠ[𝓝 x] id) :
    jac (fderiv ℝ f (g x)) * jac (fderiv ℝ g x) = 1 := by
  have hd := (hf.hasFDerivAt.comp x hg.hasFDerivAt).congr_of_eventuallyEq he.symm
  have hl : (fderiv ℝ f (g x)).comp (fderiv ℝ g x) = ContinuousLinearMap.id ℝ E4 :=
    hd.unique (hasFDerivAt_id x)
  change LinearMap.toMatrix basis basis _ * LinearMap.toMatrix basis basis _ = _
  rw [← LinearMap.toMatrix_comp]
  change LinearMap.toMatrix basis basis ((fderiv ℝ f (g x)).comp (fderiv ℝ g x)).toLinearMap = _
  rw [hl]; exact LinearMap.toMatrix_id basis

theorem pair_chart {y : E4} (hy : y ∈ exterior) :
    let K := jac (fderiv ℝ toAdvanced y)
    isotropicMetric y = K.transpose * (mg (toAdvanced y)) * K ∧
    TwoCentre.field y = K.transpose * (ff (toAdvanced y)) * K := by
  obtain ⟨hg,hF⟩ := stationary_geometry.2.2.2.2.2.2.2 y hy
  constructor
  · rw [← hg]; ext i j;unfold pullbackCoeffs
    rw [Geo.chart_der hy]
    change matrixBilin (metricCoeffs (Model.chart y)) _ _ = _
    rw [Geo.chart_coe hy];exact jac_pair _ _ _ _
  · rw [← hF]; ext i j;unfold pullbackCoeffs
    rw [Geo.chart_der hy]
    change matrixBilin (faradayCoeffs (Model.chart y)) _ _ = _
    rw [Geo.chart_coe hy];exact jac_pair _ _ _ _

theorem congr_reverse {J K A B : M4} (h : B = K.transpose * A * K) (hk : K * J = 1) :
    A = J.transpose * B * J := by
  have ht := congrArg Matrix.transpose hk
  simp only [Matrix.transpose_mul,Matrix.transpose_one] at ht
  rw [h];symm
  calc
    _ = (J.transpose*K.transpose) * A * (K*J) := by simp only [Matrix.mul_assoc]
    _ = A := by rw [ht,hk,Matrix.one_mul,Matrix.mul_one]

theorem iso_regular {y : E4} (hy : y ∈ exterior) :
    (∀ i j, SC (fun z => isotropicMetric z i j) y) ∧
    (∀ i j, SC (fun z => TwoCentre.field z i j) y) ∧
    (isotropicMetric y).det ≠ 0 := by
  have hc (b:ℝ) : SC (squaredDistance b) y := by unfold SC squaredDistance;fun_prop
  have hi (b:ℝ) (h : 0<squaredDistance b y) : SC (inverseDistance b) y :=
    (contDiffAt_const (c := (1:ℝ))).div ((hc b).sqrt h.ne') (Real.sqrt_pos.mpr h).ne'
  have hu : 0<harmonicPotential y := by unfold harmonicPotential inverseDistance;positivity
  have hs : SC harmonicPotential y := ((contDiffAt_const (c := (1:ℝ))).add (hi (-1) hy.1)).add (hi 1 hy.2)
  have he : SC electricPotential y := (contDiffAt_const (c := (1:ℝ))).div hs hu.ne'
  refine ⟨?_,?_,?_⟩
  · intro i j
    by_cases hij : i=j
    · subst j;simp only [isotropicMetric,Matrix.diagonal_apply_eq]
      by_cases hz : i=0
      · simp only [hz,if_true];exact ((contDiffAt_const (c := (1:ℝ))).div (hs.pow 2) (pow_ne_zero _ hu.ne')).neg
      · simp only [hz,if_false];exact hs.pow 2
    · simp only [isotropicMetric,Matrix.diagonal_apply_ne _ hij];exact contDiffAt_const
  · intro i j
    have hd (a : Fin 4) := partial_smooth he a
    unfold TwoCentre.field;by_cases hz : i=0 <;> by_cases hw : j=0 <;> simp only [hz,hw,if_true,if_false] <;> unfold SC <;> fun_prop
  · rw [isotropicMetric,Matrix.det_diagonal,Finset.prod_ne_zero_iff]
    intro i _;split
    · exact neg_ne_zero.mpr (div_ne_zero one_ne_zero (pow_ne_zero 2 hu.ne'))
    · exact pow_ne_zero 2 hu.ne'

theorem iso_sym (y : E4) : (isotropicMetric y).transpose = isotropicMetric y := Matrix.diagonal_transpose _
theorem iso_anti (y : E4) (a b : Fin 4) : TwoCentre.field y a b = -TwoCentre.field y b a := by unfold TwoCentre.field;ring
theorem adv_sym (z : E4) : (mg z).transpose = metricCoeffs z := by
  ext i j;change metricCoeffs z j i = metricCoeffs z i j
  have he : spatialDelta j i = spatialDelta i j := by
    unfold spatialDelta;by_cases hij : i=j <;> simp [hij,Ne.symm]
  unfold metricCoeffs;rw [he];ring

theorem adv_anti (z : E4) (a b : Fin 4) : faradayCoeffs z a b = -faradayCoeffs z b a := by unfold faradayCoeffs;ring

theorem encoded_smooth {S : Set E4} {f : E4 → ℝ} (h : ∀ x ∈ S, SC f x) :
    ContDiffOn ℝ ∞ (fun p : Pt => f (WithLp.toLp 2 p)) (encodeSet S) := by
  intro p hp;exact ((h _ hp).comp p (pack.contDiff.contDiffAt)).contDiffWithinAt

theorem encoded_open {S : Set E4} (h : IsOpen S) : IsOpen (encodeSet S) := h.preimage pack.continuous


open _root_.ExactVacuumAtlas _root_.ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell in
theorem equations (h : ∀ y ∈ exterior, EinsteinMaxwellAt isotropicMetric TwoCentre.field y) :
    ∀ z ∈ outerRegion, EinsteinMaxwellAt metricCoeffs faradayCoeffs z := by
  change ∀ z ∈ outerRegion, EinsteinMaxwellAt mg ff z
  obtain ⟨χ,hf,hb,hl,hr,hfs,hbs⟩ := Cartesian.exterior_and_frontier.2.1
  let U := encodeSet outerRegion
  let V := encodeSet exterior
  let Φ (p : Pt) := (χ (WithLp.toLp 2 p)).ofLp
  let J (p : Pt) := jac (fderiv ℝ χ (WithLp.toLp 2 p))
  let K (p : Pt) := jac (fderiv ℝ toAdvanced (χ (WithLp.toLp 2 p)))
  have hχ (z : E4) (hz : z ∈ outerRegion) : ContDiffAt ℝ ∞ χ z :=
    ((hbs z hz).contMDiffAt (Geo.outer_open.mem_nhds hz)).contDiffAt
  have hadv (x : E4) (hx : x ∈ exterior) : ContDiffAt ℝ ∞ toAdvanced x :=
    ((hfs x hx).contMDiffAt (Geo.exterior_open.mem_nhds hx)).contDiffAt
  have hback (p : Pt) (hp : p ∈ U) : J p * K p = 1 := by
    let z := WithLp.toLp 2 p
    have hx := hb hp
    have hd : DifferentiableAt ℝ χ (toAdvanced (χ z)) := by rw [hr hp];exact (hχ z hp).differentiableAt (by simp)
    have eq : χ ∘ toAdvanced =ᶠ[𝓝 (χ z)] id := Filter.mem_of_superset (Geo.exterior_open.mem_nhds hx) (fun x hx => hl hx)
    have e := jac_comp hd ((hadv _ hx).differentiableAt (by simp)) eq
    rw [hr hp] at e;exact e
  have hfor (p : Pt) (hp : p ∈ U) : K p * J p = 1 :=
    mul_eq_one_comm.mp (hback p hp)
  have hc : ExactVacuumAtlas.CoordChange U V Φ J K := by
    refine ⟨encoded_open Geo.outer_open, encoded_open Geo.exterior_open,?_, ?_, ?_, hback⟩
    · intro p hp
      exact (unpack.contDiff.contDiffAt.comp p ((hχ _ hp).comp p pack.contDiff.contDiffAt)).contDiffWithinAt
    · intro p hp;exact hb hp
    · intro p hp k i
      let L : E4 →L[ℝ] ℝ := EuclideanSpace.proj k
      have hh : HasFDerivAt (L ∘ χ) (L.comp (fderiv ℝ χ (WithLp.toLp 2 p))) (WithLp.toLp 2 (Function.update p i (p i))) := by
        simpa using (L.hasFDerivAt.comp _ ((hχ _ hp).differentiableAt (by simp)).hasFDerivAt)
      rw [show J p k i = fderiv ℝ χ (WithLp.toLp 2 p) (coordBasis i) k from jac_apply _ _ _]
      exact hh.comp_hasDerivAt (p i) (coord_slice p i)
  have hm : ExactVacuumAtlas.MetricData (enc isotropicMetric) (enc (invMetric isotropicMetric)) V := by
    refine ⟨encoded_open Geo.exterior_open,?_,?_,?_,?_⟩
    · intro p _ i j;exact congrFun (congrFun (iso_sym _) j) i
    · intro p hp;exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (iso_regular hp).2.2)
    · intro i j; exact encoded_smooth (fun y hy => (iso_regular hy).1 i j)
    · intro i j; exact encoded_smooth (fun y hy => inv_smooth (iso_regular hy).1 (iso_regular hy).2.2 i j)
  have hFs (i j : Fin 4) : ContDiffOn ℝ ∞ (enc TwoCentre.field i j) V :=
    encoded_smooth (fun y hy => (iso_regular hy).2.1 i j)
  have pair (p : Pt) (hp : p ∈ U) :
      (mg (WithLp.toLp 2 p)) = (J p).transpose * isotropicMetric (χ (WithLp.toLp 2 p)) * J p ∧
      (ff (WithLp.toLp 2 p)) = (J p).transpose * TwoCentre.field (χ (WithLp.toLp 2 p)) * J p := by
    have hh := pair_chart (hb hp)
    rw [hr hp] at hh
    exact ⟨congr_reverse hh.1 (hfor p hp),congr_reverse hh.2 (hfor p hp)⟩
  have hg (p : Pt) (hp : p ∈ U) :
      ExactVacuumAtlas.metricMatrix (enc mg) p = (J p).transpose * ExactVacuumAtlas.metricMatrix (enc isotropicMetric) (Φ p) * J p :=
    (pair p hp).1
  have hF (p : Pt) (hp : p ∈ U) :
      ExactVacuumAtlas.metricMatrix (enc ff) p = (J p).transpose * ExactVacuumAtlas.metricMatrix (enc TwoCentre.field) (Φ p) * J p :=
    (pair p hp).2
  have hgi (p : Pt) (hp : p ∈ U) :
      ExactVacuumAtlas.metricMatrix (enc (invMetric mg)) p =
      K p * ExactVacuumAtlas.metricMatrix (enc (invMetric isotropicMetric)) (Φ p) * (K p).transpose := by
    change (mg (WithLp.toLp 2 p))⁻¹ = K p * (isotropicMetric (χ (WithLp.toLp 2 p)))⁻¹ * (K p).transpose
    rw [(pair p hp).1,Matrix.mul_inv_rev,Matrix.mul_inv_rev,←Matrix.transpose_nonsing_inv,Matrix.inv_eq_right_inv (hback p hp),Matrix.mul_assoc]
  have reg (z : E4) (hz : z ∈ outerRegion) := Geo.reg_data (⟨z,⟨lt_trans (by norm_num : (3:ℝ)/4<1) hz.1,hz.2⟩⟩ : manifold)
  have gs (z : E4) (hz : z ∈ outerRegion) (i j : Fin 4) : SC (fun x => mg x i j) z := ((reg z hz).1 i j).of_le (by simp)
  have fs (z : E4) (hz : z ∈ outerRegion) (i j : Fin 4) : SC (fun x => ff x i j) z := ((reg z hz).2.2.1 i j).of_le (by simp)
  have eqs (q : Pt) (hq : q ∈ V) :
      (∀ i j, einsteinMaxwell (enc isotropicMetric) (enc (invMetric isotropicMetric)) (enc TwoCentre.field) i j q = 0) ∧
      (∀ i, maxwellDiv (enc isotropicMetric) (enc (invMetric isotropicMetric)) (enc TwoCentre.field) i q = 0) ∧
      (∀ i j k, faradayCyclic (enc TwoCentre.field) i j k q = 0) := by
    have hx : WithLp.toLp 2 q ∈ exterior := hq
    have src := h _ hx
    have rs := iso_regular hx
    have E (i j : Fin 4) : einsteinMaxwell (enc isotropicMetric) (enc (invMetric isotropicMetric)) (enc TwoCentre.field) i j q = 0 := by
      rw [ein_bridge Geo.exterior_open (fun y hy => (iso_regular hy).1) (fun y _ => iso_sym y) hx rs.2.2,src.1 i j,sub_self]
    have D (i : Fin 4) : maxwellDiv (enc isotropicMetric) (enc (invMetric isotropicMetric)) (enc TwoCentre.field) i q=0 := by
      have e := div_bridge Geo.exterior_open (fun y _ => iso_sym y) hx rs.1 rs.2.1 rs.2.2 (iso_anti _) i
      have hd : divDensity isotropicMetric TwoCentre.field i (WithLp.toLp 2 q)=0 := src.2.1 i
      have hv : volume isotropicMetric (WithLp.toLp 2 q) ≠ 0 := (Real.sqrt_pos.mpr (abs_pos.mpr rs.2.2)).ne'
      exact (mul_eq_zero.mp (e.symm.trans hd)).resolve_left hv
    have B (i j k : Fin 4) : faradayCyclic (enc TwoCentre.field) i j k q=0 := (cyclic_bridge rs.2.1 i j k).trans (src.2.2 i j k)
    exact ⟨E,D,B⟩
  let srcSol : ChartSolution V := {
    metric := enc isotropicMetric
    inverse := enc (invMetric isotropicMetric)
    field := enc TwoCentre.field
    regular := hm
    smoothField := hFs
    skew := fun q _ i j => iso_anti _ i j
    einstein := fun q hq => (eqs q hq).1
    maxwell := fun q hq => (eqs q hq).2.1
    closed := fun q hq => (eqs q hq).2.2 }
  let advSol := srcSol.rechart hc (enc mg) (enc (invMetric mg)) (enc ff) hg hgi hF
  intro z hz
  let p : Pt := z.ofLp
  have hp : p ∈ U := hz
  have hx : WithLp.toLp 2 (Φ p) ∈ exterior := hb hp
  have src := h _ hx
  have rs := iso_regular hx
  have hn : (mg z).det ≠ 0 := by
    have e := congrArg Matrix.det (pair p hp).1
    simp only [Matrix.det_mul,Matrix.det_transpose] at e
    change (mg (WithLp.toLp 2 p)).det ≠ 0
    rw [e]
    exact mul_ne_zero (mul_ne_zero (Matrix.det_ne_zero_of_right_inverse (hback p hp)) rs.2.2) (Matrix.det_ne_zero_of_right_inverse (hback p hp))
  refine ⟨?_,?_,?_⟩
  · intro i j
    exact sub_eq_zero.mp ((ein_bridge (G:=mg) (F:=ff) (p:=p) Geo.outer_open gs (fun y _ => adv_sym y) hp hn i j).symm.trans (advSol.einstein p hp i j))
  · intro j
    change divDensity mg ff j (WithLp.toLp 2 p) = 0
    rw [div_bridge (G:=mg) (F:=ff) (p:=p) Geo.outer_open (fun y _ => adv_sym y) hp (gs z hz) (fs z hz) hn (adv_anti _) j]
    exact mul_eq_zero_of_right _ (advSol.maxwell p hp j)
  · intro a b c
    exact (cyclic_bridge (p:=p) (fs z hz) a b c).symm.trans (advSol.closed p hp a b c)

end
end NoHair.TwoCentre.Model.Transport
open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Cartesian _root_.NoHair.TwoCentre.Model
open NoHair NoHair.TwoCentre NoHair.TwoCentre.Cartesian NoHair.TwoCentre.Model

theorem checkedResult (h : ∀ y ∈ exterior, EinsteinMaxwellAt isotropicMetric TwoCentre.field y) :
    ∀ z ∈ outerRegion, EinsteinMaxwellAt metricCoeffs faradayCoeffs z := Transport.equations h
end ElectrovacProof025

alias NoHair.TwoCentre.Model.advanced_exterior_equations := ElectrovacProof025.checkedResult


namespace ElectrovacProof026

open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Model
open NoHair NoHair.TwoCentre NoHair.TwoCentre.Model

theorem checkedResult (h : ∀ y ∈ exterior, EinsteinMaxwellAt isotropicMetric TwoCentre.field y) :
    IsElectrovac metric faraday := electrovac_across_horizon (advanced_exterior_equations h)
end ElectrovacProof026

alias NoHair.TwoCentre.Model.electrovac_in_advanced_atlas := ElectrovacProof026.checkedResult


namespace ElectrovacProof027

open _root_.NoHair _root_.NoHair.KNE
open NoHair NoHair.KNE Set Filter Topology

namespace NoHair.TwoCentre.Isotropic
open _root_.NoHair _root_.NoHair.TwoCentre

noncomputable section

export _root_.TwoCentreEndDecay.NoHair.TwoCentre.Isotropic (disp)

export _root_.TwoCentreEndDecay.NoHair.TwoCentre.Isotropic (delta)

export _root_.TwoCentreEndDecay.NoHair.TwoCentre.Isotropic (radius)

export _root_.TwoCentreEndDecay.NoHair.TwoCentre.Isotropic (poleGrad)

def poleHess (c : ℝ) (i k : Fin 4) (y : E4) : ℝ :=
  -delta i k / radius c y ^ 3 + 3 * disp c i y * disp c k y / radius c y ^ 5
export _root_.TwoCentreEndDecay.NoHair.TwoCentre.Isotropic (grad)

def hess (i k : Fin 4) (y : E4) := poleHess (-1) i k y + poleHess 1 i k y

theorem exterior_open : IsOpen exterior := by
  have hs (c : ℝ) : Continuous (squaredDistance c) := by unfold squaredDistance; fun_prop
  exact (isOpen_lt continuous_const (hs (-1))).inter (isOpen_lt continuous_const (hs 1))

export _root_.TwoCentreEndDecay.NoHair.TwoCentre.Isotropic (U_pos)

theorem cp_congr {f g : E4 → ℝ} {y : E4} (h : f =ᶠ[𝓝 y] g) (i : Fin 4) :
    coordPartial f i y = coordPartial g i y := by
  unfold coordPartial
  rw [h.fderiv_eq]

export _root_.TwoCentreEndDecay.NoHair.TwoCentre.Isotropic (diff_disp)

export _root_.TwoCentreEndDecay.NoHair.TwoCentre.Isotropic (diff_sqrt)

export _root_.TwoCentreEndDecay.NoHair.TwoCentre.Isotropic (diff_radius)

export _root_.TwoCentreEndDecay.NoHair.TwoCentre.Isotropic (diff_pole)

theorem diff_poleGrad (c : ℝ) (i : Fin 4) {y : E4} (hy : 0 < squaredDistance c y) :
    HasCP (poleGrad c i) y (fun k => poleHess c i k y) := by
  have hr : 0 < radius c y := Real.sqrt_pos.2 hy
  apply ((diff_disp c i y).neg.div ((diff_radius c hy).pow 3) (pow_ne_zero 3 hr.ne')).congr_d
  intro k
  unfold poleHess
  field_simp [hr.ne']
  ring

export _root_.TwoCentreEndDecay.NoHair.TwoCentre.Isotropic (diff_U)

theorem diff_grad (i : Fin 4) {y : E4} (hy : y ∈ exterior) :
    HasCP (grad i) y (fun k => hess i k y) :=
  (diff_poleGrad (-1) i hy.1).add (diff_poleGrad 1 i hy.2)

theorem grad_time (y : E4) : grad 0 y = 0 := by simp [grad, poleGrad, disp]

theorem hess_time (i : Fin 4) (y : E4) : hess 0 i y = 0 := by
  simp [hess, poleHess, delta, disp]

theorem hess_symm (i k : Fin 4) (y : E4) : hess i k y = hess k i y := by
  have hd : delta i k = delta k i := by
    by_cases h : i = k
    · rw [h]
    · simp [delta, h, Ne.symm h]
  simp only [hess, poleHess, hd]
  ring

theorem pole_trace (c : ℝ) {y : E4} (hy : 0 < squaredDistance c y) :
    poleHess c 1 1 y + poleHess c 2 2 y + poleHess c 3 3 y = 0 := by
  have hr : 0 < radius c y := Real.sqrt_pos.2 hy
  have hs : radius c y ^ 2 = (y 1 - c) ^ 2 + y 2 ^ 2 + y 3 ^ 2 :=
    Real.sq_sqrt hy.le
  change -1 / radius c y ^ 3 + 3 * (y 1 - c) * (y 1 - c) / radius c y ^ 5 +
    (-1 / radius c y ^ 3 + 3 * y 2 * y 2 / radius c y ^ 5) +
    (-1 / radius c y ^ 3 + 3 * y 3 * y 3 / radius c y ^ 5) = 0
  field_simp [hr.ne']
  linear_combination -3 * hs

theorem laplace_U {y : E4} (hy : y ∈ exterior) : hess 1 1 y + hess 2 2 y + hess 3 3 y = 0 := by
  unfold hess
  linarith [pole_trace (-1) hy.1, pole_trace 1 hy.2]

export _root_.TwoCentreEndDecay.NoHair.TwoCentre.Isotropic (field_values)

end
end NoHair.TwoCentre.Isotropic

open _root_.NoHair _root_.NoHair.KNE
open NoHair NoHair.KNE Set Filter Topology Matrix
open scoped BigOperators

namespace NoHair.TwoCentre.Isotropic
open _root_.NoHair _root_.NoHair.TwoCentre

noncomputable section

def inverseEntry (u : ℝ) (i : Fin 4) : ℝ := if i = 0 then -u ^ 2 else 1 / u ^ 2

theorem inverse_metric (y : E4) :
    invMetric isotropicMetric y = Matrix.diagonal (inverseEntry (harmonicPotential y)) := by
  apply Matrix.inv_eq_right_inv
  rw [isotropicMetric, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  ext i
  have hn := (U_pos y).ne'
  by_cases hi : i = 0 <;> simp [inverseEntry, hi, hn]

theorem metric_volume (y : E4) :
    Real.sqrt |(isotropicMetric y).det| = harmonicPotential y ^ 2 := by
  have hn := (U_pos y).ne'
  have hd : (isotropicMetric y).det = -(harmonicPotential y ^ 4) := by
    rw [isotropicMetric, Matrix.det_diagonal, Fin.prod_univ_four]
    simp (config := {decide := true})
    field_simp
  rw [hd, abs_neg, abs_of_nonneg (by positivity), show harmonicPotential y ^ 4 =
    (harmonicPotential y ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]

theorem raised (y : E4) (i j : Fin 4) :
    raiseBoth isotropicMetric field y i j =
      inverseEntry (harmonicPotential y) i * inverseEntry (harmonicPotential y) j * field y i j := by
  classical
  simp [raiseBoth, inverse_metric, Matrix.diagonal_apply, ite_mul, mul_ite, mul_assoc]

theorem densitized {y : E4} (hy : y ∈ exterior) (i j : Fin 4) :
    Real.sqrt |(isotropicMetric y).det| * raiseBoth isotropicMetric field y i j =
      (if j = 0 then grad i y else 0) - (if i = 0 then grad j y else 0) := by
  have h := (U_pos y).ne'
  rw [metric_volume, raised, field_values hy]
  unfold inverseEntry
  split_ifs <;> subst_vars <;> field_simp [h] <;> ring

def electricGrad (i : Fin 4) (y : E4) := grad i y / harmonicPotential y ^ 2
def electricHess (i k : Fin 4) (y : E4) :=
  hess i k y / harmonicPotential y ^ 2 - 2 * grad i y * grad k y / harmonicPotential y ^ 3

theorem diff_electricGrad (i : Fin 4) {y : E4} (hy : y ∈ exterior) :
    HasCP (electricGrad i) y (fun k => electricHess i k y) := by
  have h := (U_pos y).ne'
  apply ((diff_grad i hy).div ((diff_U hy).pow 2) (pow_ne_zero 2 h)).congr_d
  intro k
  unfold electricHess
  field_simp [h]
  ring

theorem electricHess_symm (i k : Fin 4) (y : E4) :
    electricHess i k y = electricHess k i y := by
  unfold electricHess
  rw [hess_symm i k]
  ring

theorem dfield {y : E4} (hy : y ∈ exterior) (i j k : Fin 4) :
    coordPartial (fun z => field z i j) k y =
      (if i = 0 then electricHess j k y else 0) - (if j = 0 then electricHess i k y else 0) := by
  have hh : (fun z => field z i j) =ᶠ[𝓝 y] (fun z =>
      (if i = 0 then electricGrad j z else 0) - (if j = 0 then electricGrad i z else 0)) :=
    by filter_upwards [exterior_open.mem_nhds hy] with z hz using field_values hz i j
  rw [cp_congr hh]
  split_ifs
  · exact ((diff_electricGrad j hy).sub (diff_electricGrad i hy)).eq k
  · exact ((diff_electricGrad j hy).sub (HasCP.cst 0 y)).eq k
  · exact ((HasCP.cst 0 y).sub (diff_electricGrad i hy)).eq k
  · exact ((HasCP.cst 0 y).sub (HasCP.cst 0 y)).eq k

theorem dflux {y : E4} (hy : y ∈ exterior) (i j : Fin 4) :
    coordPartial (fun z => Real.sqrt |(isotropicMetric z).det| * raiseBoth isotropicMetric field z i j) i y =
      (if j = 0 then hess i i y else 0) - (if i = 0 then hess j i y else 0) := by
  have hh : (fun z => Real.sqrt |(isotropicMetric z).det| * raiseBoth isotropicMetric field z i j) =ᶠ[𝓝 y]
      (fun z => (if j = 0 then grad i z else 0) - (if i = 0 then grad j z else 0)) :=
    by filter_upwards [exterior_open.mem_nhds hy] with z hz using densitized hz i j
  rw [cp_congr hh]
  split_ifs
  · exact ((diff_grad i hy).sub (diff_grad j hy)).eq i
  · exact ((diff_grad i hy).sub (HasCP.cst 0 y)).eq i
  · exact ((HasCP.cst 0 y).sub (diff_grad j hy)).eq i
  · exact ((HasCP.cst 0 y).sub (HasCP.cst 0 y)).eq i

theorem maxwell_equations {y : E4} (hy : y ∈ exterior) :
    (∀ ν, ∑ μ, coordPartial
      (fun z => Real.sqrt |(isotropicMetric z).det| * raiseBoth isotropicMetric field z μ ν) μ y = 0) ∧
    (∀ l μ ν, coordPartial (fun z => field z μ ν) l y + coordPartial (fun z => field z ν l) μ y
      + coordPartial (fun z => field z l μ) ν y = 0) := by
  constructor
  · intro ν
    simp only [dflux hy, Fin.sum_univ_four]
    have ht (i) : hess i 0 y = 0 := (hess_symm i 0 y).trans (hess_time i y)
    by_cases h : ν = 0 <;> simp (config := {decide := true}) [h, ht, laplace_U hy]
  · intro l μ ν
    simp only [dfield hy]
    rw [electricHess_symm ν l, electricHess_symm μ l, electricHess_symm ν μ]
    split_ifs <;> ring

end
end NoHair.TwoCentre.Isotropic

open _root_.NoHair _root_.NoHair.KNE
open NoHair NoHair.KNE Set Filter Topology Matrix
open scoped BigOperators

namespace NoHair.TwoCentre.Isotropic
open _root_.NoHair _root_.NoHair.TwoCentre

noncomputable section

export _root_.TwoCentreEndDecay.NoHair.TwoCentre.Isotropic (metricSlope)

export _root_.TwoCentreEndDecay.NoHair.TwoCentre.Isotropic (dmetric)

def gammaNumerator (p : Fin 4 → ℝ) (i j k : Fin 4) : ℝ :=
  if i = 0 then -((if j = 0 then p k else 0) + (if k = 0 then p j else 0))
  else if j = 0 then (if k = 0 then -p i else 0)
  else if k = 0 then 0
  else (if i = k then p j else 0) + (if i = j then p k else 0) - (if j = k then p i else 0)

def gammaPower (i j k : Fin 4) : ℕ := if i ≠ 0 ∧ j = 0 ∧ k = 0 then 5 else 1

def gammaValue (u : ℝ) (p : Fin 4 → ℝ) (i j k : Fin 4) : ℝ :=
  gammaNumerator p i j k / u ^ gammaPower i j k

def gammaDerivative (u : ℝ) (p hp : Fin 4 → ℝ) (i j k l : Fin 4) : ℝ :=
  let n := gammaPower i j k
  (gammaNumerator hp i j k * u ^ n -
    gammaNumerator p i j k * (n * u ^ (n - 1) * p l)) / (u ^ n) ^ 2

theorem christoffel_value {y : E4} (hy : y ∈ exterior) (i j k : Fin 4) :
    christoffel isotropicMetric y i j k =
      gammaValue (harmonicPotential y) (fun l => grad l y) i j k := by
  have hn := (U_pos y).ne'
  simp only [christoffel, inverse_metric, Matrix.diagonal_apply, dmetric hy]
  simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp (config := {decide := true}) [metricSlope, inverseEntry, gammaValue, gammaNumerator,
      gammaPower, grad_time] <;> field_simp [hn]

theorem diff_numerator {y : E4} (hy : y ∈ exterior) (i j k : Fin 4) :
    HasCP (fun z => gammaNumerator (fun l => grad l z) i j k) y
      (fun s => gammaNumerator (fun l => hess l s y) i j k) := by
  unfold gammaNumerator
  split_ifs <;> repeat' first
    | exact diff_grad _ hy
    | exact HasCP.cst 0 _
    | apply HasCP.neg
    | apply HasCP.sub
    | apply HasCP.add

theorem dchristoffel {y : E4} (hy : y ∈ exterior) (i j k l : Fin 4) :
    coordPartial (fun z => christoffel isotropicMetric z i j k) l y =
      gammaDerivative (harmonicPotential y) (fun s => grad s y) (fun s => hess s l y) i j k l := by
  have he : (fun z => christoffel isotropicMetric z i j k) =ᶠ[𝓝 y]
      (fun z => gammaValue (harmonicPotential z) (fun s => grad s z) i j k) := by
    filter_upwards [exterior_open.mem_nhds hy] with z hz using christoffel_value hz i j k
  rw [cp_congr he]
  exact ((diff_numerator hy i j k).div ((diff_U hy).pow (gammaPower i j k))
    (pow_ne_zero _ (U_pos y).ne')).eq l

end
end NoHair.TwoCentre.Isotropic

open _root_.NoHair
open NoHair Set Topology Matrix
open scoped BigOperators

namespace NoHair.TwoCentre.Isotropic
open _root_.NoHair _root_.NoHair.TwoCentre

noncomputable section

def gradSq (p : Fin 4 → ℝ) := p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2

def ricciValue (u : ℝ) (p : Fin 4 → ℝ) (i j : Fin 4) : ℝ :=
  if i = 0 then (if j = 0 then gradSq p / u ^ 6 else 0)
  else if j = 0 then 0 else ((if i = j then gradSq p else 0) - 2 * p i * p j) / u ^ 2

set_option maxHeartbeats 4500000 in
theorem ricci_formula {y : E4} (hy : y ∈ exterior) (i j : Fin 4) :
    ricci isotropicMetric y i j = ricciValue (harmonicPotential y) (fun k => grad k y) i j := by
  have hu := (U_pos y).ne'
  have ht (k) : hess k 0 y = 0 := (hess_symm k 0 y).trans (hess_time k y)
  have h21 := hess_symm 2 1 y
  have h31 := hess_symm 3 1 y
  have h32 := hess_symm 3 2 y
  have h33 : hess 3 3 y = -(hess 1 1 y + hess 2 2 y) := by linarith [laplace_U hy]
  simp only [ricci, riemann, dchristoffel hy, christoffel_value hy]
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [Fin.sum_univ_four, gammaDerivative, gammaValue, gammaPower,
      gammaNumerator, ricciValue, gradSq, grad_time, ht, hess_time, h21, h31, h32, h33] <;>
    field_simp [hu] <;> ring

theorem scalar_zero {y : E4} (hy : y ∈ exterior) : scalarCurvature isotropicMetric y = 0 := by
  have hu := (U_pos y).ne'
  simp (config := {decide := true}) [scalarCurvature, Fin.sum_univ_four, inverse_metric,
    Matrix.diagonal_apply, inverseEntry, ricci_formula hy, ricciValue, gradSq]
  field_simp [hu]
  ring

set_option maxHeartbeats 1800000 in
theorem source_formula {y : E4} (hy : y ∈ exterior) (i j : Fin 4) :
    maxwellSource isotropicMetric field y i j =
      ricciValue (harmonicPotential y) (fun k => grad k y) i j := by
  have hu := (U_pos y).ne'
  simp only [maxwellSource, inverse_metric, raised, field_values hy]
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [Fin.sum_univ_four, Matrix.diagonal_apply, isotropicMetric,
      inverseEntry, ricciValue, gradSq, grad_time] <;> field_simp [hu] <;> ring

/-- The exact coordinate Einstein–Maxwell equations of the no-hair mission hold
throughout the two-centre isotropic exterior. -/
theorem exterior_electrovac (y : E4) (hy : y ∈ exterior) :
    EinsteinMaxwellAt isotropicMetric field y := by
  refine ⟨?_, maxwell_equations hy⟩
  intro i j
  rw [einsteinTensor, scalar_zero hy, mul_zero, zero_mul, sub_zero, ricci_formula hy, source_formula hy]

end
end NoHair.TwoCentre.Isotropic

open _root_.NoHair _root_.NoHair.KNE
open NoHair NoHair.KNE Set Matrix

namespace NoHair.TwoCentre.Isotropic
open _root_.NoHair _root_.NoHair.TwoCentre

noncomputable section

export _root_.TwoCentreEndDecay.NoHair.TwoCentre.Isotropic (radius_from_infinity)

export _root_.TwoCentreEndDecay.NoHair.TwoCentre.Isotropic (displacement_le)

export _root_.TwoCentreEndDecay.NoHair.TwoCentre.Isotropic (far_pole_bounds)

export _root_.TwoCentreEndDecay.NoHair.TwoCentre.Isotropic (asymptotic_decay)

end
end NoHair.TwoCentre.Isotropic

open _root_.NoHair _root_.NoHair.TwoCentre
open NoHair NoHair.TwoCentre NoHair.TwoCentre.Isotropic

theorem checkedResult :
    (∀ y ∈ exterior, EinsteinMaxwellAt isotropicMetric field y) ∧
    (∀ y : E4, 2 < spatialRadius y → y ∈ exterior ∧ ∀ i j k,
      |isotropicMetric y i j - minkowski i j| ≤ 64 / spatialRadius y ∧
      |coordPartial (fun z => isotropicMetric z i j) k y| ≤ 64 / spatialRadius y ^ 2 ∧
      |field y i j| ≤ 64 / spatialRadius y ^ 2) :=
  ⟨fun y hy => exterior_electrovac y hy, fun _ hy => asymptotic_decay hy⟩
end ElectrovacProof027

alias NoHair.TwoCentre.isotropic_electrovac_and_decay := ElectrovacProof027.checkedResult


namespace ElectrovacProof028

open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Cartesian _root_.NoHair.TwoCentre.Model
open NoHair NoHair.TwoCentre NoHair.TwoCentre.Cartesian NoHair.TwoCentre.Model Set Topology
open scoped ContDiff Manifold RealInnerProductSpace

namespace NoHair.TwoCentre.Model.Curves
open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Model

noncomputable section

export _root_.ElectrovacProof003.NoHair.TwoCentre.Model.Curves (radialSpeed)

export _root_.ElectrovacProof003.NoHair.TwoCentre.Model.Curves (spatial_inner)

export _root_.ElectrovacProof003.NoHair.TwoCentre.Model.Curves (radialSpeed_coords)

export _root_.ElectrovacProof003.NoHair.TwoCentre.Model.Curves (metric_eval)

export _root_.ElectrovacProof003.NoHair.TwoCentre.Model.Curves (angular_unit)

def spatialL : E4 →L[ℝ] E3 := LinearMap.toContinuousLinearMap {
  toFun := spatial
  map_add' := fun v w => by ext i; rfl
  map_smul' := fun c v => by ext i; rfl }

set_option backward.isDefEq.respectTransparency false in
theorem norm_curve_deriv {γ : ℝ → manifold} {t : ℝ}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E4) 1 γ) :
    HasDerivAt (fun s => ‖spatial (γ s)‖ - 1) (radialSpeed (γ t) (velocity γ t)) t := by
  have hval : HasMFDerivAt 𝓘(ℝ, E4) 𝓘(ℝ, E4) (Subtype.val : manifold → E4) (γ t)
      (ContinuousLinearMap.id ℝ E4) := by
    have hs : MDifferentiableAt 𝓘(ℝ, E4) 𝓘(ℝ, E4) (Subtype.val : manifold → E4) (γ t) := (contMDiff_subtype_val (n := (1 : ℕ∞ω)) (U := manifold) (I := 𝓘(ℝ, E4))).mdifferentiableAt one_ne_zero
    have he : mfderiv 𝓘(ℝ, E4) 𝓘(ℝ, E4) (Subtype.val : manifold → E4) (γ t) =
        ContinuousLinearMap.id ℝ E4 := mfderiv_extChartAt_self (I := 𝓘(ℝ, E4)) (x := γ t)
    exact he ▸ hs.hasMFDerivAt
  have compDer : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E4) (fun s => (γ s : E4)) t
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E4) γ t : ℝ →L[ℝ] E4) := by
    exact hval.comp t (hγ.mdifferentiableAt one_ne_zero).hasMFDerivAt
  have hcoord : HasDerivAt (fun s => (γ s : E4)) (velocity γ t : E4) t :=
    (hasMFDerivAt_iff_hasFDerivAt.mp compDer).hasDerivAt
  have hspace : HasDerivAt (fun s => spatial (γ s)) (spatial (velocity γ t)) t :=
    spatialL.hasFDerivAt.comp_hasDerivAt t hcoord
  have hz : (3 : ℝ) / 4 < ‖spatial (γ t)‖ := (γ t).property.1
  have hn : 0 < ‖spatial (γ t)‖ := by linarith
  have hnorm := (hspace.norm_sq.sqrt (pow_ne_zero 2 hn.ne')).sub_const 1
  simp only [Real.sqrt_sq (norm_nonneg _)] at hnorm
  convert! hnorm using 1
  rw [radialSpeed, angularDirection, real_inner_smul_left]
  field_simp

theorem actual_inward (z : manifold) {v : E4}
    (hh : ‖spatial z‖ = 1) (hf : IsFutureTimelike metric orientation z v) : radialSpeed z v < 0 := by
  let c := angularDirection z 0
  let w := radialSpeed z v
  let a := 1 / (1 + c ^ 2)
  have hp : parameters z = (0, c) := Prod.ext (by change ‖spatial z‖ - 1 = 0; rw [hh]; norm_num) rfl
  obtain ⟨hvv, hvr, hrr, hang⟩ := Advanced.regular_horizon.2.1 c
  have hunit := angular_unit z
  have hdir : spatial (orientation z) = -a • angularDirection z := by
    simp [orientation, Model.spatial_coordinates, hp, hvr, hrr, a]
  let vo : E4 := orientation z
  have htime : vo 0 = 1 := rfl
  have hspeed : radialSpeed z (orientation z) = -a := by
    change ⟪angularDirection z, spatial vo⟫ = -a
    rw [hdir, real_inner_smul_right, real_inner_self_eq_norm_sq, hunit]
    ring
  have ht := hf.1
  have hfut : metric z v vo < 0 := hf.2
  rw [metric_eval, hp, hvv, hvr, hrr, hang, hh, real_inner_self_eq_norm_sq] at ht
  rw [metric_eval, hp, hvv, hvr, hrr, hang, hh, htime, hspeed, hdir,
    real_inner_smul_right, real_inner_comm (angularDirection z) (spatial v)] at hfut
  have hA : w ^ 2 ≤ ‖spatial v‖ ^ 2 := by
    have h := abs_real_inner_le_norm (angularDirection z) (spatial v)
    rw [hunit, one_mul] at h
    exact sq_le_sq' (abs_le.mp h).1 (abs_le.mp h).2
  change radialSpeed z v < 0
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : c * a < 2 := by
    dsimp [a]
    rw [mul_one_div, div_lt_iff₀ (by positivity)]
    nlinarith [sq_nonneg (c - 1 / 4)]
  change w < 0
  by_contra! hnon
  have hvineq : -a * v 0 + (1 - c * a) * w < 0 := by
    dsimp [w, radialSpeed] at hfut ⊢
    linarith
  have htineq : 2 * v 0 * w + c * w ^ 2 < 0 := by
    dsimp [w] at hA ⊢
    nlinarith
  nlinarith [mul_lt_mul_of_pos_left htineq ha, mul_nonpos_of_nonpos_of_nonneg hvineq.le hnon,
    mul_nonneg (sub_nonneg.mpr hb.le) (sq_nonneg w)]

theorem no_escape (γ : ℝ → manifold) (hγ : IsFutureTimelikeCurveIn metric orientation univ γ)
    (hstart : γ 0 ∉ outer) : γ 1 ∉ outer := by
  let r := fun t => ‖spatial (γ t)‖ - 1
  have h0 : r 0 ≤ 0 := by
    have h : ¬ 1 < ‖spatial (γ 0)‖ := fun h => hstart ⟨h, (γ 0).property.2⟩
    exact sub_nonpos.mpr (le_of_not_gt h)
  have hn := Advanced.regular_horizon.2.2 r
    (continuous_iff_continuousAt.mpr (fun t => (norm_curve_deriv (t := t) hγ.1).continuousAt)) h0 (by
      intro t ht hr
      have hh : ‖spatial (γ t)‖ = 1 := sub_eq_zero.mp hr
      have hw := actual_inward (γ t) hh ((hγ.2 t ht).2)
      refine ⟨0, 1, radialSpeed (γ t) (velocity γ t), 0, norm_curve_deriv hγ.1,
        le_rfl, by linarith, by linarith⟩)
  intro h
  exact (not_lt_of_ge (sub_nonpos.mp hn)) h.1

end
end NoHair.TwoCentre.Model.Curves

open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Model
open NoHair.TwoCentre.Model.Curves

theorem checkedResult (γ : ℝ → manifold) (hγ : IsFutureTimelikeCurveIn metric orientation univ γ)
    (hstart : γ 0 ∉ outer) : γ 1 ∉ outer := ElectrovacProof028.NoHair.TwoCentre.Model.Curves.no_escape γ hγ hstart
end ElectrovacProof028

alias NoHair.TwoCentre.Model.no_escape := ElectrovacProof028.checkedResult


namespace ElectrovacProof029

open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Cartesian _root_.NoHair.TwoCentre.Model
open NoHair NoHair.TwoCentre NoHair.TwoCentre.Cartesian NoHair.TwoCentre.Model Set Topology
open scoped ContDiff Manifold RealInnerProductSpace

namespace NoHair.TwoCentre.Model.Curves
open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Model

noncomputable section

export _root_.ElectrovacProof003.NoHair.TwoCentre.Model.Curves (radialSpeed)

export _root_.ElectrovacProof003.NoHair.TwoCentre.Model.Curves (spatial_inner)

export _root_.ElectrovacProof003.NoHair.TwoCentre.Model.Curves (radialSpeed_coords)

export _root_.ElectrovacProof003.NoHair.TwoCentre.Model.Curves (metric_eval)

export _root_.ElectrovacProof003.NoHair.TwoCentre.Model.Curves (angular_unit)

end
end NoHair.TwoCentre.Model.Curves


open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Cartesian _root_.NoHair.TwoCentre.Model
open NoHair NoHair.TwoCentre NoHair.TwoCentre.Cartesian NoHair.TwoCentre.Model Set Filter Topology
open scoped ContDiff Manifold RealInnerProductSpace BigOperators

namespace NoHair.TwoCentre.Model.Signals
open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Model

noncomputable section

theorem spatial_cont : Continuous spatial := by
  have h : ContDiff ℝ ∞ spatial := contDiff_euclidean.2 (fun i => contDiff_piLp_apply (p := 2) (i := i.succ))
  exact h.continuous

theorem outer_open : IsOpen Model.outer := by
  have h : IsOpen outerRegion := (isOpen_lt continuous_const spatial_cont.norm).inter
    (isOpen_ne_fun spatial_cont continuous_const)
  exact h.preimage continuous_subtype_val

theorem outer_subset : outerRegion ⊆ spacetime := by
  intro z hz
  exact ⟨lt_trans (by norm_num) hz.1, hz.2⟩

theorem model_chart_val {y : E4} (hy : y ∈ exterior) :
    (Model.chart y : E4) = toAdvanced y := by
  obtain ⟨_, hmap, _⟩ := Cartesian.exterior_and_frontier.2.1
  simp [Model.chart, outer_subset (hmap hy)]

theorem model_chart_diffeo : IsDiffeoOnto Model.chart exterior Model.outer := by
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

theorem exterior_isOpen : IsOpen exterior := by
  have h (c : ℝ) : Continuous (squaredDistance c) := by unfold squaredDistance; fun_prop
  exact (isOpen_lt continuous_const (h (-1))).inter (isOpen_lt continuous_const (h 1))

private abbrev L (y : E4) := mfderiv 𝓘(ℝ, E4) 𝓘(ℝ, E4) Model.chart y

theorem L_onto {y : E4} (hy : y ∈ exterior) : Function.Surjective (L y) := by
  obtain ⟨χ, hmap, hinv, hleft, hright, hs, ht⟩ := model_chart_diffeo
  have hx := hmap hy
  have hcomp : (Model.chart ∘ χ) =ᶠ[𝓝 (Model.chart y)] id :=
    Filter.mem_of_superset (outer_open.mem_nhds hx) (fun _ hz => hright hz)
  have hf := ((hs _ (hinv hx)).contMDiffAt (exterior_isOpen.mem_nhds (hinv hx))).mdifferentiableAt (by simp)
  have hi := ((ht _ hx).contMDiffAt (outer_open.mem_nhds hx)).mdifferentiableAt (by simp)
  have hder : mfderiv 𝓘(ℝ, E4) 𝓘(ℝ, E4) (Model.chart ∘ χ) (Model.chart y) =
      ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ, E4) (Model.chart y)) := hcomp.mfderiv_eq.trans mfderiv_id
  rw [mfderiv_comp _ hf hi, hleft hy] at hder
  intro v
  exact ⟨mfderiv 𝓘(ℝ, E4) 𝓘(ℝ, E4) χ (Model.chart y) v, DFunLike.congr_fun hder v⟩

theorem Upos (y : E4) : 0 < harmonicPotential y := by
  have h (c : ℝ) : 0 ≤ inverseDistance c y := by unfold inverseDistance; positivity
  unfold harmonicPotential
  linarith [h (-1), h 1]

theorem metric_pullback {y : E4} (hy : y ∈ exterior) (v w : E4) :
    metric (Model.chart y) (L y v) (L y w) = -(v 0 * w 0) / harmonicPotential y ^ 2 +
      harmonicPotential y ^ 2 * ⟪spatial v, spatial w⟫ := by
  obtain ⟨_, _, _, _, _, _, _, hmatch⟩ := Model.stationary_geometry
  let B : E4 →L[ℝ] E4 →L[ℝ] ℝ := metric (Model.chart y)
  let A : E4 →L[ℝ] E4 := L y
  have expand (x : E4) : ∑ i, x i • coordBasis i = x := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply, coordBasis] using
      (EuclideanSpace.basisFun (Fin 4) ℝ).sum_repr x
  have hbas (i j : Fin 4) : B (A (coordBasis i)) (A (coordBasis j)) = isotropicMetric y i j :=
    congrFun (congrFun (hmatch y hy).1 i) j
  change B (A v) (A w) = _
  calc
    _ = B (A (∑ i, v i • coordBasis i)) (A (∑ i, w i • coordBasis i)) := by rw [expand v, expand w]
    _ = _ := by
      simp only [Curves.spatial_inner, Fin.sum_univ_four]
      simp (config := {decide := true}) [hbas, isotropicMetric]
      ring

theorem chart_time {y : E4} (hy : y ∈ exterior) : L y (coordBasis 0) = (coordBasis 0 : E4) := by
  have hreg (s : ℝ) : y + s • coordBasis 0 ∈ exterior := by
    simpa (config := {decide := true}) [exterior, squaredDistance, coordBasis] using hy
  have hs (s : ℝ) : spatial (y + s • coordBasis 0) = spatial y := by ext i; simp [spatial, coordBasis]
  have ht (s : ℝ) : (Model.chart (y + s • coordBasis 0) : E4) = (Model.chart y : E4) + s • coordBasis 0 := by
    rw [model_chart_val (hreg s), model_chart_val hy]
    simp only [toAdvanced, hs]
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [coordinates, coordBasis]
      ring
    · simp [coordinates, coordBasis]
  have h0 : y + (0 : ℝ) • coordBasis 0 = y := by simp
  have hγ : HasDerivAt (fun s : ℝ => y + s • coordBasis 0) (coordBasis 0) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (coordBasis 0)).const_add y
  have ⟨_, _, _, _, _, smooth, _⟩ := model_chart_diffeo
  let b := Model.chart y
  have hval : HasMFDerivAt 𝓘(ℝ, E4) 𝓘(ℝ, E4) (Subtype.val : manifold → E4) b
      (ContinuousLinearMap.id ℝ E4) := by
    have d : MDifferentiableAt 𝓘(ℝ, E4) 𝓘(ℝ, E4) (Subtype.val : manifold → E4) b :=
      contMDiff_subtype_val.mdifferentiableAt (n := (1 : ℕ∞ω)) one_ne_zero
    have he : mfderiv 𝓘(ℝ, E4) 𝓘(ℝ, E4) (Subtype.val : manifold → E4) b =
        ContinuousLinearMap.id ℝ E4 := mfderiv_extChartAt_self (I := 𝓘(ℝ, E4)) (x := b)
    exact he ▸ d.hasMFDerivAt
  have df : HasFDerivAt (fun z => (Model.chart z : E4)) (L y : E4 →L[ℝ] E4) y :=
    hasMFDerivAt_iff_hasFDerivAt.mp (hval.comp y
      (((smooth y hy).contMDiffAt (exterior_isOpen.mem_nhds hy)).mdifferentiableAt (by simp)).hasMFDerivAt)
  have df0 : HasFDerivAt (fun z => (Model.chart z : E4)) (L y : E4 →L[ℝ] E4) (y + (0 : ℝ) • coordBasis 0) := by rwa [h0]
  have hact := HasFDerivAt.comp_hasDerivAt (l := fun z : E4 => (Model.chart z : E4))
    (f := fun s : ℝ => y + s • coordBasis 0) (0 : ℝ) df0 hγ
  simp only [Function.comp_def] at hact
  have hdes : HasDerivAt (fun s : ℝ => (Model.chart y : E4) + s • coordBasis 0) (coordBasis 0) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (coordBasis 0)).const_add (Model.chart y : E4)
  rw [show (fun s : ℝ => (Model.chart (y + s • coordBasis 0) : E4)) = _ from funext ht] at hact
  exact hact.unique hdes

theorem time_orientation_pair (z : manifold) (hz : z ∈ Model.outer) :
    metric z (coordBasis 0) (orientation z) < 0 := by
  let p := parameters z
  have hpr : 0 < p.1 := sub_pos.mpr hz.1
  have hH : 0 < Advanced.H p := by
    have hd : 0 ≤ 1 / Advanced.distanceToOther p := by unfold Advanced.distanceToOther; positivity
    unfold Advanced.H
    nlinarith [mul_nonneg hpr.le (show 0 ≤ 1 + 1 / Advanced.distanceToOther p by linarith)]
  have hH0 : 0 < Advanced.H₀ p := by unfold Advanced.H₀; linarith
  have hvr : 0 < Advanced.gvr p := by unfold Advanced.gvr; positivity
  have hvv : Advanced.gvv p < 0 := div_neg_of_neg_of_pos (neg_lt_zero.mpr (sq_pos_of_pos hpr)) (sq_pos_of_pos hH)
  let a := Advanced.gvr p / (1 + Advanced.grr p ^ 2)
  have ha : 0 < a := by dsimp [a]; positivity
  let T : E4 := orientation z
  have hT : spatial T = -a • angularDirection z := Model.spatial_coordinates _ _
  have hVT : T 0 = 1 := rfl
  have hn : Curves.radialSpeed z T = -a := by
    change ⟪angularDirection z, spatial T⟫ = -a
    rw [hT, real_inner_smul_right, real_inner_self_eq_norm_sq, Curves.angular_unit]
    ring
  have hs0 : spatial (coordBasis 0) = 0 := by ext i; simp [spatial, coordBasis]
  have h0 : Curves.radialSpeed z (coordBasis 0) = 0 := by simp [Curves.radialSpeed, hs0]
  change metric z (coordBasis 0) T < 0
  rw [Curves.metric_eval, hVT, h0, hn, hs0, inner_zero_left]
  change Advanced.gvv p * 1 * 1 + Advanced.gvr p * (1 * -a + 0 * 1) + _ * 0 * -a + _ * (0 - 0 * -a) < 0
  nlinarith [mul_pos ha hvr]

theorem orient_isotropic {y : E4} (hy : y ∈ exterior) (v : E4)
    (hv : 0 < v 0) (ht : harmonicPotential y ^ 2 * ‖spatial v‖ < v 0) :
    IsFutureTimelike metric orientation (Model.chart y) (L y v) := by
  let u := harmonicPotential y
  have hu : 0 < u := Upos y
  have hs0 : spatial (coordBasis 0) = 0 := by ext i; simp [spatial, coordBasis]
  have ⟨_, hm, _⟩ := model_chart_diffeo
  obtain ⟨_, _, _, _, hor, _⟩ := Model.stationary_geometry
  obtain ⟨w₀, hw₀⟩ := L_onto hy (orientation (Model.chart y))
  let w : E4 := w₀
  have hw : L y w = orientation (Model.chart y) := hw₀
  have hww := (metric_pullback hy w w).symm.trans_lt (show metric (Model.chart y) (L y w) (L y w) < 0 by
    rw [hw]; exact hor.2 _)
  rw [real_inner_self_eq_norm_sq] at hww
  have htkw : metric (Model.chart y) (L y (coordBasis 0)) (L y w) < 0 := by
    rw [chart_time hy, hw]; exact time_orientation_pair _ (hm hy)
  have hwt := (metric_pullback hy (coordBasis 0) w).symm.trans_lt htkw
  rw [hs0, inner_zero_left] at hwt
  have hwpos : 0 < w 0 := by
    change -(1 * w 0) / u ^ 2 + u ^ 2 * 0 < 0 at hwt
    simp only [one_mul, mul_zero, add_zero, neg_div, neg_lt_zero] at hwt
    exact (div_pos_iff_of_pos_right (sq_pos_of_pos hu)).mp hwt
  have hwfast : u ^ 2 * ‖spatial w‖ < w 0 := by
    have hsq := (lt_div_iff₀ (sq_pos_of_pos hu)).mp (show u ^ 2 * ‖spatial w‖ ^ 2 < (w 0 * w 0) / u ^ 2 by
      change -(w 0 * w 0) / u ^ 2 + u ^ 2 * ‖spatial w‖ ^ 2 < 0 at hww
      rw [neg_div] at hww
      linarith)
    nlinarith [mul_nonneg (sq_nonneg u) (norm_nonneg (spatial w))]
  change u ^ 2 * ‖spatial v‖ < v 0 at ht
  have gneg (a b : E4) (ha : u ^ 2 * ‖spatial a‖ < a 0)
      (hb : u ^ 2 * ‖spatial b‖ < b 0) (hb' : 0 < b 0) :
      metric (Model.chart y) (L y a) (L y b) < 0 := by
    rw [metric_pullback hy]
    have hmul := mul_le_mul_of_nonneg_left hb.le (mul_nonneg (sq_nonneg u) (norm_nonneg (spatial a)))
    have hmul' := mul_lt_mul_of_pos_right ha hb'
    have hinner := real_inner_le_norm (spatial a) (spatial b)
    change -(a 0 * b 0) / u ^ 2 + u ^ 2 * ⟪spatial a, spatial b⟫ < 0
    have hcrit : u ^ 2 * ⟪spatial a, spatial b⟫ < a 0 * b 0 / u ^ 2 := by
      apply (lt_div_iff₀ (sq_pos_of_pos hu)).mpr
      nlinarith [mul_le_mul_of_nonneg_left hinner (sq_nonneg (u ^ 2))]
    rw [neg_div]
    linarith
  exact ⟨gneg v v ht ht hv, hw ▸ gneg v w ht hwfast hwpos⟩

theorem affine_timelike (y v : E4) (hreg : ∀ s : ℝ, y + s • v ∈ exterior) (hv : 0 < v 0)
    (hb : ∀ t ∈ Icc (0 : ℝ) 1, harmonicPotential (y + t • v) ^ 2 * ‖spatial v‖ < v 0) :
    IsFutureTimelikeCurveIn metric orientation univ (fun s : ℝ => Model.chart (y + s • v)) := by
  obtain ⟨_, _, _, _, _, hs, _⟩ := model_chart_diffeo
  let q := fun s : ℝ => y + s • v
  have ds (s : ℝ) : ContMDiffAt 𝓘(ℝ, E4) 𝓘(ℝ, E4) ∞ Model.chart (q s) :=
    (hs _ (hreg s)).contMDiffAt (exterior_isOpen.mem_nhds (hreg s))
  have dq : ContDiff ℝ ∞ q := by dsimp [q]; fun_prop
  refine ⟨fun s => ((ds s).of_le (by simp)).comp s ((dq.of_le (by simp)).contMDiff s), ?_⟩
  intro t ht
  refine ⟨mem_univ _, ?_⟩
  have ha : HasDerivAt q v t := by simpa [q] using ((hasDerivAt_id t).smul_const v).const_add y
  have dL : velocity (fun s : ℝ => Model.chart (y + s • v)) t = L (q t) v := by
    unfold velocity L
    change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E4) (Model.chart ∘ q) t 1 = _
    rw [mfderiv_comp _ ((ds t).mdifferentiableAt (by simp)) (dq.contMDiff.mdifferentiableAt (by simp)),
      mfderiv_eq_fderiv]
    exact congrArg (fun a : E4 => L (q t) a) ((ha.differentiableAt.hasFDerivAt.hasDerivAt).unique ha)
  rw [dL]
  exact orient_isotropic (hreg t) v hv (hb t ht)

theorem line_avoids_poles {y : E4} (hy : y ∈ exterior) :
    ∃ k : Fin 4, k ≠ 0 ∧ ∀ s : ℝ, y + s • coordBasis k ∈ exterior := by
  by_cases ha : y 2 = 0 ∧ y 3 = 0
  · refine ⟨2, by decide, ?_⟩
    have h (c : ℝ) (hc : 0 < squaredDistance c y) (s : ℝ) : 0 < squaredDistance c (y + s • coordBasis 2) := by
      simp (config := {decide := true}) [squaredDistance, coordBasis, ha.1, ha.2] at hc ⊢
      nlinarith [sq_nonneg s]
    exact fun s => ⟨h _ hy.1 s, h _ hy.2 s⟩
  · refine ⟨1, by decide, ?_⟩
    have hperp : 0 < y 2 ^ 2 + y 3 ^ 2 := by
      by_cases h : y 2 = 0
      · have hz : y 3 ≠ 0 := fun hz => ha ⟨h, hz⟩
        linarith [sq_pos_of_ne_zero hz, sq_nonneg (y 2)]
      · linarith [sq_pos_of_ne_zero h, sq_nonneg (y 3)]
    have h (c s : ℝ) : 0 < squaredDistance c (y + s • coordBasis 1) := by
      simp (config := {decide := true}) [squaredDistance, coordBasis]
      nlinarith [sq_nonneg (y 1 + s - c)]
    exact fun s => ⟨h _ s, h _ s⟩

theorem spatial_radius_bound (y : E4) {k : Fin 4} (hk : k ≠ 0) : |y k| ≤ spatialRadius y := by
  have hR : 0 ≤ spatialRadius y := Real.sqrt_nonneg _
  have hR2 : spatialRadius y ^ 2 = y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2 := Real.sq_sqrt (by positivity)
  rw [← sq_le_sq₀ (abs_nonneg _) hR, sq_abs]
  fin_cases k
  · exact False.elim (hk rfl)
  · change y 1 ^ 2 ≤ _
    linarith [sq_nonneg (y 2), sq_nonneg (y 3)]
  · change y 2 ^ 2 ≤ _
    linarith [sq_nonneg (y 1), sq_nonneg (y 3)]
  · change y 3 ^ 2 ≤ _
    linarith [sq_nonneg (y 1), sq_nonneg (y 2)]

theorem U_cont {z : E4} (hz : z ∈ exterior) : ContinuousAt harmonicPotential z := by
  have h (c : ℝ) (hc : 0 < squaredDistance c z) : ContinuousAt (inverseDistance c) z := by
    unfold inverseDistance
    apply continuousAt_const.div
    · unfold squaredDistance
      fun_prop
    · exact (Real.sqrt_pos.mpr hc).ne'
  exact (continuousAt_const.add (h (-1) hz.1)).add (h 1 hz.2)

theorem temporal_shift (u : E4) (s : ℝ) (c : ℝ) :
    squaredDistance c (u + s • coordBasis 0) = squaredDistance c u := by
  simp (config := {decide := true}) [squaredDistance, coordBasis]

theorem signals_at {y : E4} (hy : y ∈ exterior) :
    Model.chart y ∈ chronoPastSet metric orientation (Model.chart '' exteriorRegion 2) ∧
    Model.chart y ∈ chronoFutureSet metric orientation (Model.chart '' exteriorRegion 2) := by
  obtain ⟨k, hk, hline⟩ := line_avoids_poles hy
  let d := |y k| + 3
  let x (s : ℝ) := y + (s * d) • coordBasis k
  let b := ‖spatial (d • coordBasis k)‖
  have hcx : Continuous x := by dsimp [x]; fun_prop
  have hcb : ContinuousOn (fun s => harmonicPotential (x s) ^ 2 * b) (Icc (-1 : ℝ) 1) := by
    intro s _
    have hr : x s ∈ exterior := hline (s * d)
    exact ((((U_cont hr).comp (f := x) hcx.continuousAt).pow 2).mul continuousAt_const).continuousWithinAt
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image hcb
  have hBd (s : ℝ) (hs : s ∈ Icc (-1 : ℝ) 1) : harmonicPotential (x s) ^ 2 * b ≤ B := hB ⟨s, hs, rfl⟩
  have hB0 : 0 ≤ B := (mul_nonneg (sq_nonneg _) (norm_nonneg _)).trans (hBd 0 (by constructor <;> norm_num))
  let v := d • coordBasis k + (B + 1) • coordBasis 0
  have hv0 : v 0 = B + 1 := by simp [v, coordBasis, Ne.symm hk]
  have hvsp : spatial v = spatial (d • coordBasis k) := by ext i; simp [v, spatial, coordBasis]
  have hpath (t : ℝ) : y + t • v = x t + (t * (B + 1)) • coordBasis 0 := by
    dsimp [v, x]
    rw [smul_add, smul_smul, smul_smul, add_assoc]
  have hreg (t : ℝ) : y + t • v ∈ exterior := by
    rw [hpath]
    exact ⟨(temporal_shift _ _ _).symm ▸ (hline (t * d)).1, (temporal_shift _ _ _).symm ▸ (hline (t * d)).2⟩
  have hU (t : ℝ) : harmonicPotential (y + t • v) = harmonicPotential (x t) := by
    simp only [hpath, harmonicPotential, inverseDistance, temporal_shift]
  have hbound (s : ℝ) (hs : s ∈ Icc (-1 : ℝ) 1) : harmonicPotential (y + s • v) ^ 2 * ‖spatial v‖ < v 0 := by
    rw [hU, hvsp, hv0]
    exact lt_of_le_of_lt (hBd s hs) (by linarith)
  have hv : 0 < v 0 := by rw [hv0]; linarith
  have hf := affine_timelike y v hreg hv (fun t ht => hbound t ⟨by linarith [ht.1], ht.2⟩)
  have hback (t : ℝ) : (y - v) + t • v = y + (t - 1) • v := by rw [sub_smul, one_smul]; abel
  have hb := affine_timelike (y - v) v (fun s => (hback s).symm ▸ hreg (s - 1)) hv (fun t ht => by
    rw [hback]; exact hbound _ ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  have hvk : v k = d := by simp [v, coordBasis, hk]
  have hfar : y + (1 : ℝ) • v ∈ exteriorRegion 2 := by
    have h := (le_abs_self _).trans (spatial_radius_bound (y + (1 : ℝ) • v) hk)
    simp only [one_smul, PiLp.add_apply, hvk] at h
    change 2 < spatialRadius _
    simp only [one_smul]
    dsimp [d] at h
    linarith [(abs_le.mp (le_refl |y k|)).1]
  have hfar' : y - v ∈ exteriorRegion 2 := by
    have h := (neg_le_abs _).trans (spatial_radius_bound (y - v) hk)
    simp only [PiLp.sub_apply, hvk] at h
    change 2 < spatialRadius _
    dsimp [d] at h
    linarith [le_abs_self (y k)]
  constructor
  · refine mem_iUnion.mpr ⟨Model.chart (y + (1 : ℝ) • v), mem_iUnion.mpr ⟨⟨_, hfar, rfl⟩, ?_⟩⟩
    exact ⟨_, hf, by simp, rfl⟩
  · refine mem_iUnion.mpr ⟨Model.chart (y - v), mem_iUnion.mpr ⟨⟨_, hfar', rfl⟩, ?_⟩⟩
    exact ⟨_, hb, by simp, by simp⟩

/-- Chronological communication with the far end on the full two-centre exterior. -/
theorem exterior_signals : Model.outer ⊆ chronoPastSet metric orientation (Model.chart '' exteriorRegion 2) ∧
    Model.outer ⊆ chronoFutureSet metric orientation (Model.chart '' exteriorRegion 2) := by
  obtain ⟨χ, _, hh, _, hr, _⟩ := model_chart_diffeo
  constructor <;> intro z hz
  · exact hr hz ▸ (signals_at (hh hz)).1
  · exact hr hz ▸ (signals_at (hh hz)).2

end
end NoHair.TwoCentre.Model.Signals

open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Model
open NoHair.TwoCentre.Model.Signals

theorem checkedResult :
    chronoPastSet metric orientation (Model.chart '' exteriorRegion 2) = outer ∧
    outer ⊆ chronoFutureSet metric orientation (Model.chart '' exteriorRegion 2) := by
  refine ⟨Subset.antisymm ?_ exterior_signals.1, exterior_signals.2⟩
  intro p hp
  obtain ⟨q, hq⟩ := mem_iUnion.mp hp
  obtain ⟨hq, hpq⟩ := mem_iUnion.mp hq
  obtain ⟨γ, ht, hstart, hend⟩ := hpq
  obtain ⟨_, hmap, _⟩ := model_chart_diffeo
  have hqout : q ∈ Model.outer := by
    obtain ⟨y, hy, rfl⟩ := hq
    exact hmap (isotropic_electrovac_and_decay.2 y hy).1
  by_contra hn
  exact Model.no_escape γ ht (hstart ▸ hn) (hend ▸ hqout)
end ElectrovacProof029

alias NoHair.TwoCentre.Model.chronological_access := ElectrovacProof029.checkedResult


namespace ElectrovacProof030

open Set
open scoped RealInnerProductSpace

namespace NoHair.TwoCentre

private abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- Integrate a speed bound by a time derivative on the segment. -/
theorem travel_bound {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {x dx : ℝ → V} {τ dτ : ℝ → ℝ}
    (hx : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt x (dx t) t)
    (hτ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt τ (dτ t) t)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, ‖dx t‖ ≤ dτ t)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : ‖x s - x 0‖ ≤ τ s - τ 0 := by
  let f t := x t - x 0
  let B t := τ t - τ 0
  have hf (t) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt f (dx t) t :=
    (hx t ht).sub_const _
  have hB (t) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt B (dτ t) t :=
    (hτ t ht).sub_const _
  exact image_norm_le_of_norm_deriv_right_le_deriv_boundary'
    (fun t ht => (hf t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hf t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (by simp [f, B]) (fun t ht => (hB t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hB t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (fun t ht => hbound t (Ico_subset_Icc_self ht)) hs

theorem inverse_distance_deriv {x : ℝ → Space} {dx b : Space} {t : ℝ}
    (hx : HasDerivAt x dx t) (hne : x t ≠ b) :
    HasDerivAt (fun s => 1 / ‖x s - b‖) (-⟪x t - b, dx⟫ / ‖x t - b‖ ^ 3) t := by
  have hn := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne)
  have hsq := ((hx.sub_const b).norm_sq).sqrt (pow_ne_zero 2 hn)
  simp only [Real.sqrt_sq (norm_nonneg _)] at hsq
  have hh := (hasDerivAt_const t (1 : ℝ)).fun_div hsq hn
  convert! hh using 1
  field_simp [hn]
  ring

theorem pole_bound {x dx : ℝ → Space} {τ dτ : ℝ → ℝ} {b : Space}
    (hx : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt x (dx t) t)
    (hτ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt τ (dτ t) t)
    (hreg : ∀ t ∈ Icc (0 : ℝ) 1, x t ≠ b)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, (1 / ‖x t - b‖) ^ 2 * ‖dx t‖ ≤ dτ t)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    1 / ‖x s - b‖ ≤ 1 / ‖x 0 - b‖ + (τ s - τ 0) := by
  have h := travel_bound (fun t ht => inverse_distance_deriv (hx t ht) (hreg t ht)) hτ
    (fun t ht => ?_) hs
  · have hle := le_abs_self (1 / ‖x s - b‖ - 1 / ‖x 0 - b‖)
    rw [Real.norm_eq_abs] at h
    linarith
  · have hn : 0 < ‖x t - b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hreg t ht))
    rw [Real.norm_eq_abs, abs_div, abs_neg, abs_of_pos (pow_pos hn 3)]
    refine le_trans ?_ (hbound t ht)
    rw [div_le_iff₀ (pow_pos hn 3)]
    calc
      _ ≤ ‖x t - b‖ * ‖dx t‖ := abs_real_inner_le_norm _ _
      _ = _ := by field_simp [hn.ne']

end NoHair.TwoCentre

open NoHair.TwoCentre

/-- On the two-centre exterior, finite coordinate time confines every optical
causal path to a compact set a positive distance from both poles. -/
theorem checkedResult
    (b₁ b₂ x₀ : EuclideanSpace ℝ (Fin 3)) (h₁ : x₀ ≠ b₁) (h₂ : x₀ ≠ b₂)
    (L : ℝ) (hL : 0 ≤ L) :
    ∃ K : Set (EuclideanSpace ℝ (Fin 3)), IsCompact K ∧ b₁ ∉ K ∧ b₂ ∉ K ∧
    ∀ (x dx : ℝ → EuclideanSpace ℝ (Fin 3)) (τ dτ : ℝ → ℝ),
      x 0 = x₀ →
      (∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt x (dx t) t ∧ HasDerivAt τ (dτ t) t ∧
        x t ≠ b₁ ∧ x t ≠ b₂ ∧
        (1 + 1 / ‖x t - b₁‖ + 1 / ‖x t - b₂‖) ^ 2 * ‖dx t‖ ≤ dτ t) →
      ∀ s ∈ Icc (0 : ℝ) 1, τ s - τ 0 ≤ L → x s ∈ K := by
  let R (b : EuclideanSpace ℝ (Fin 3)) := 1 / (1 / ‖x₀ - b‖ + L)
  have hR (b) (hb : x₀ ≠ b) : 0 < R b := by
    have : 0 < ‖x₀ - b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hb)
    dsimp [R]
    positivity
  let K := (Metric.closedBall x₀ L ∩ {z | R b₁ ≤ ‖z - b₁‖}) ∩ {z | R b₂ ≤ ‖z - b₂‖}
  have hclosed (b) : IsClosed {z | R b ≤ ‖z - b‖} :=
    isClosed_le continuous_const (continuous_id.sub continuous_const).norm
  refine ⟨K, ((isCompact_closedBall x₀ L).inter_right (hclosed b₁)).inter_right (hclosed b₂),
    ?_, ?_, ?_⟩
  · intro h
    have hh : R b₁ ≤ ‖b₁ - b₁‖ := h.1.2
    simpa using (hR b₁ h₁).not_ge (by simpa using hh)
  · intro h
    have hh : R b₂ ≤ ‖b₂ - b₂‖ := h.2
    simpa using (hR b₂ h₂).not_ge (by simpa using hh)
  · intro x dx τ dτ hx₀ hpath s hs htime
    have hx t ht := (hpath t ht).1
    have hτ t ht := (hpath t ht).2.1
    let U t := 1 + 1 / ‖x t - b₁‖ + 1 / ‖x t - b₂‖
    have hspeed (t) (ht : t ∈ Icc (0 : ℝ) 1) (k : ℝ) (hk : 0 ≤ k) (hu : k ≤ U t) :
        k ^ 2 * ‖dx t‖ ≤ dτ t :=
      (mul_le_mul_of_nonneg_right (sq_le_sq' (by linarith) hu) (norm_nonneg _)).trans
        (hpath t ht).2.2.2.2
    have hu (t : ℝ) : 1 ≤ U t ∧ 1 / ‖x t - b₁‖ ≤ U t ∧ 1 / ‖x t - b₂‖ ≤ U t := by
      dsimp [U]
      have ha : 0 ≤ 1 / ‖x t - b₁‖ := by positivity
      have hb : 0 ≤ 1 / ‖x t - b₂‖ := by positivity
      exact ⟨by linarith, by linarith, by linarith⟩
    have hball := travel_bound hx hτ (fun t ht => by
      simpa using hspeed t ht 1 (by norm_num) (hu t).1) hs
    rw [hx₀] at hball
    have hradius (b) (hb : x₀ ≠ b) (hxreg : ∀ t ∈ Icc (0 : ℝ) 1, x t ≠ b)
        (hUb : ∀ t, 1 / ‖x t - b‖ ≤ U t) : R b ≤ ‖x s - b‖ := by
      have hbnd := pole_bound hx hτ hxreg (fun t ht => hspeed t ht _ (by positivity) (hUb t)) hs
      rw [hx₀] at hbnd
      have hp : 0 < ‖x s - b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hxreg s hs))
      have hinv : 1 / ‖x s - b‖ ≤ 1 / ‖x₀ - b‖ + L := by linarith
      have hp₀ : 0 < ‖x₀ - b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hb)
      apply (div_le_iff₀ (show 0 < 1 / ‖x₀ - b‖ + L by positivity)).2
      linarith [(div_le_iff₀ hp).1 hinv]
    exact ⟨⟨by simpa [Metric.mem_closedBall, dist_eq_norm] using hball.trans htime,
      hradius b₁ h₁ (fun t ht => (hpath t ht).2.2.1) (fun t => (hu t).2.1)⟩,
      hradius b₂ h₂ (fun t ht => (hpath t ht).2.2.2.1) (fun t => (hu t).2.2)⟩

end ElectrovacProof030

alias NoHair.TwoCentre.optical_confinement := ElectrovacProof030.checkedResult


namespace ElectrovacProof031

open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Cartesian _root_.NoHair.TwoCentre.Model
open NoHair NoHair.TwoCentre NoHair.TwoCentre.Cartesian NoHair.TwoCentre.Model Set Topology
open scoped ContDiff Manifold RealInnerProductSpace

namespace NoHair.TwoCentre.Model.Curves
open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Model

noncomputable section

export _root_.ElectrovacProof003.NoHair.TwoCentre.Model.Curves (radialSpeed)

export _root_.ElectrovacProof003.NoHair.TwoCentre.Model.Curves (spatial_inner)

export _root_.ElectrovacProof003.NoHair.TwoCentre.Model.Curves (radialSpeed_coords)

export _root_.ElectrovacProof003.NoHair.TwoCentre.Model.Curves (metric_eval)

export _root_.ElectrovacProof003.NoHair.TwoCentre.Model.Curves (angular_unit)

end
end NoHair.TwoCentre.Model.Curves


open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Cartesian _root_.NoHair.TwoCentre.Model
open NoHair NoHair.TwoCentre NoHair.TwoCentre.Cartesian NoHair.TwoCentre.Model Set Filter Topology
open scoped ContDiff Manifold RealInnerProductSpace BigOperators

namespace NoHair.TwoCentre.Model.Signals
open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Model

noncomputable section

export _root_.ElectrovacProof029.NoHair.TwoCentre.Model.Signals (spatial_cont)

export _root_.ElectrovacProof029.NoHair.TwoCentre.Model.Signals (outer_open)

export _root_.ElectrovacProof029.NoHair.TwoCentre.Model.Signals (outer_subset)

export _root_.ElectrovacProof029.NoHair.TwoCentre.Model.Signals (model_chart_val)

export _root_.ElectrovacProof029.NoHair.TwoCentre.Model.Signals (model_chart_diffeo)

export _root_.ElectrovacProof029.NoHair.TwoCentre.Model.Signals (exterior_isOpen)

export _root_.ElectrovacProof029.NoHair.TwoCentre.Model.Signals (L)

export _root_.ElectrovacProof029.NoHair.TwoCentre.Model.Signals (L_onto)

export _root_.ElectrovacProof029.NoHair.TwoCentre.Model.Signals (Upos)

export _root_.ElectrovacProof029.NoHair.TwoCentre.Model.Signals (metric_pullback)

export _root_.ElectrovacProof029.NoHair.TwoCentre.Model.Signals (chart_time)

export _root_.ElectrovacProof029.NoHair.TwoCentre.Model.Signals (time_orientation_pair)

noncomputable def iso : manifold → E4 := Classical.choose model_chart_diffeo
theorem iso_spec :
    MapsTo Model.chart exterior Model.outer ∧ MapsTo iso Model.outer exterior ∧
    LeftInvOn iso Model.chart exterior ∧ RightInvOn iso Model.chart Model.outer ∧
    ContMDiffOn 𝓘(ℝ, E4) 𝓘(ℝ, E4) ∞ Model.chart exterior ∧
    ContMDiffOn 𝓘(ℝ, E4) 𝓘(ℝ, E4) ∞ iso Model.outer := Classical.choose_spec model_chart_diffeo

theorem optical_future {y : E4} (hy : y ∈ exterior) (v : E4)
    (hf : IsFutureCausal metric orientation (Model.chart y) (L y v)) :
    0 < v 0 ∧ harmonicPotential y ^ 2 * ‖spatial v‖ ≤ v 0 := by
  let u := harmonicPotential y
  have hu : 0 < u := Upos y
  have hs0 : spatial (coordBasis 0) = 0 := by ext i; simp [spatial, coordBasis]
  obtain ⟨_, hm, _⟩ := model_chart_diffeo
  obtain ⟨_, _, _, _, hor, _⟩ := Model.stationary_geometry
  obtain ⟨w₀, hw₀⟩ := L_onto hy (orientation (Model.chart y))
  let w : E4 := w₀
  have hw : L y w = orientation (Model.chart y) := hw₀
  have hww := (metric_pullback hy w w).symm.trans_lt (show metric (Model.chart y) (L y w) (L y w) < 0 by
    rw [hw]; exact hor.2 _)
  have hwt := (metric_pullback hy (coordBasis 0) w).symm.trans_lt
    (show metric (Model.chart y) (L y (coordBasis 0)) (L y w) < 0 by
      rw [chart_time hy, hw]; exact time_orientation_pair _ (hm hy))
  rw [hs0, inner_zero_left] at hwt
  have hwpos : 0 < w 0 := by
    change -(1 * w 0) / u ^ 2 + u ^ 2 * 0 < 0 at hwt
    simpa [neg_div, hu.le, div_pos_iff_of_pos_right (sq_pos_of_pos hu)] using hwt
  rw [real_inner_self_eq_norm_sq] at hww
  have bound (a : E4) (hn : -(a 0 * a 0) / u ^ 2 + u ^ 2 * ‖spatial a‖ ^ 2 ≤ 0) :
      u ^ 2 * ‖spatial a‖ ≤ |a 0| := by
    have hsq := (le_div_iff₀ (sq_pos_of_pos hu)).mp (show u ^ 2 * ‖spatial a‖ ^ 2 ≤ (a 0 * a 0) / u ^ 2 by
      rw [neg_div] at hn; linarith)
    nlinarith [sq_abs (a 0), abs_nonneg (a 0), mul_nonneg (sq_nonneg u) (norm_nonneg (spatial a))]
  have hwbound : u ^ 2 * ‖spatial w‖ ≤ w 0 := (abs_of_pos hwpos) ▸ bound w hww.le
  have hvv := (metric_pullback hy v v).symm.trans_le hf.2.1
  rw [real_inner_self_eq_norm_sq] at hvv
  have hvbound := bound v hvv
  have hvpos : 0 < v 0 := by
    by_contra! hvneg
    rw [abs_of_nonpos hvneg] at hvbound
    have hi := (abs_le.mp (abs_real_inner_le_norm (spatial v) (spatial w))).1
    have hp := mul_le_mul hvbound hwbound (mul_nonneg (sq_nonneg u) (norm_nonneg _)) (neg_nonneg.mpr hvneg)
    have hpair := (metric_pullback hy v w).symm.trans_lt (show metric (Model.chart y) (L y v) (L y w) < 0 by
      rw [hw]; exact hf.2.2)
    change -(v 0 * w 0) / u^2 + u^2 * ⟪spatial v, spatial w⟫ < 0 at hpair
    rw [neg_div] at hpair
    have hpair' := (lt_div_iff₀ (sq_pos_of_pos hu)).mp
      (show u ^ 2 * ⟪spatial v, spatial w⟫ < v 0 * w 0 / u ^ 2 by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hi (sq_nonneg (u ^ 2))]
  exact ⟨hvpos, (abs_of_pos hvpos) ▸ hvbound⟩

def isoV (γ : ℝ → manifold) (t : ℝ) : E4 :=
  mfderiv 𝓘(ℝ, E4) 𝓘(ℝ, E4) iso (γ t) (velocity γ t)

set_option backward.isDefEq.respectTransparency false in
theorem lift_causal {γ : ℝ → manifold}
    (h : IsFutureCausalCurveIn metric orientation Model.outer γ) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    HasDerivAt (fun s => iso (γ s)) (isoV γ t) t ∧ iso (γ t) ∈ exterior ∧
    0 < isoV γ t 0 ∧ harmonicPotential (iso (γ t)) ^ 2 * ‖spatial (isoV γ t)‖ ≤ isoV γ t 0 := by
  obtain ⟨_, hb, _, hr, hs, hi⟩ := iso_spec
  have hz := (h.2 t ht).1
  have hy := hb hz
  have hchi := ((hi _ hz).contMDiffAt (outer_open.mem_nhds hz)).mdifferentiableAt (by simp)
  have hchart := ((hs _ hy).contMDiffAt (exterior_isOpen.mem_nhds hy)).mdifferentiableAt (by simp)
  have hcurve := (h.1.mdifferentiableAt (by simp) (x := t)).hasMFDerivAt
  have hcomp : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E4) (iso ∘ γ) t
      ((mfderiv 𝓘(ℝ, E4) 𝓘(ℝ, E4) iso (γ t)).comp (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E4) γ t)) :=
    hchi.hasMFDerivAt.comp t hcurve
  have der : HasDerivAt (fun s => iso (γ s)) (isoV γ t) t :=
    (hasMFDerivAt_iff_hasFDerivAt.mp hcomp).hasDerivAt
  have he : (Model.chart ∘ iso) =ᶠ[𝓝 (γ t)] id :=
    Filter.mem_of_superset (outer_open.mem_nhds hz) (fun x hx => hr hx)
  have hD : mfderiv 𝓘(ℝ, E4) 𝓘(ℝ, E4) (Model.chart ∘ iso) (γ t) =
      ContinuousLinearMap.id ℝ E4 := he.mfderiv_eq.trans mfderiv_id
  rw [mfderiv_comp _ hchart hchi] at hD
  have hdv : L (iso (γ t)) (isoV γ t) = velocity γ t := DFunLike.congr_fun hD _
  have hca : IsFutureCausal metric orientation (Model.chart (iso (γ t))) (L (iso (γ t)) (isoV γ t)) := by
    rw [hdv, hr hz]
    exact (h.2 t ht).2
  exact ⟨der,hy,optical_future hy _ hca⟩

def clock (z : manifold) := iso z 0

theorem interval_strict {γ : ℝ → manifold}
    (h : IsFutureCausalCurveIn metric orientation Model.outer γ) :
    StrictMonoOn (fun t => clock (γ t)) (Icc (0 : ℝ) 1) := by
  have hh (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun s => clock (γ s)) (isoV γ t 0) t := by
    exact (PiLp.proj (p := 2) (β := fun _ : Fin 4 => ℝ) 0).hasFDerivAt.comp_hasDerivAt t (lift_causal h ht).1
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (fun t ht => (hh t ht).continuousAt.continuousWithinAt)
  intro t ht
  have ht' := interior_subset ht
  rw [(hh t ht').deriv]
  exact (lift_causal h ht').2.2.1

theorem future_clock {p q : manifold} (hq : q ∈ causalFuture metric orientation Model.outer p) :
    clock p ≤ clock q := by
  rcases hq with eq | ⟨γ,h,hs,he⟩
  · exact le_of_eq (congrArg clock eq.symm)
  · have hlt := interval_strict h (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one) zero_lt_one
    simpa [hs,he] using hlt.le

theorem spatial_dist (c : ℝ) (y : E4) :
    ‖spatial y - c • unitAxis‖ ^ 2 = squaredDistance c y := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  simp [spatial, unitAxis, squaredDistance, PiLp.sub_apply, PiLp.smul_apply]

theorem iso_regular (y : E4) :
    y ∈ exterior ↔ spatial y ≠ -unitAxis ∧ spatial y ≠ unitAxis := by
  change 0 < squaredDistance (-1) y ∧ 0 < squaredDistance 1 y ↔ _
  rw [← spatial_dist, ← spatial_dist, neg_one_smul, one_smul]
  simp only [sq_pos_iff, norm_ne_zero_iff, sub_ne_zero]

theorem optical_factor (y : E4) :
    harmonicPotential y = 1 + 1 / ‖spatial y - (-unitAxis)‖ + 1 / ‖spatial y - unitAxis‖ := by
  unfold harmonicPotential inverseDistance
  simp [← spatial_dist, Real.sqrt_sq (norm_nonneg _)]

theorem spatial_deriv {f : ℝ → E4} {v : E4} {t : ℝ} (hd : HasDerivAt f v t) :
    HasDerivAt (fun s => spatial (f s)) (spatial v) t := by
  let A : E4 →L[ℝ] E3 := LinearMap.toContinuousLinearMap {
    toFun := spatial, map_add' := fun _ _ => by ext; rfl, map_smul' := fun _ _ => by ext; rfl }
  exact A.hasFDerivAt.comp_hasDerivAt t hd

theorem time_deriv {f : ℝ → E4} {v : E4} {t : ℝ} (hd : HasDerivAt f v t) :
    HasDerivAt (fun s => f s 0) (v 0) t :=
  (PiLp.proj (p := 2) (β := fun _ : Fin 4 => ℝ) 0).hasFDerivAt.comp_hasDerivAt t hd

theorem join_coords (z : E4) : coordinates (z 0) (spatial z) = z := by
  ext i
  exact Fin.cases rfl (fun _ => rfl) i

theorem coord_cont : Continuous (fun p : ℝ × E3 => coordinates p.1 p.2) := by
  have h : ContDiff ℝ ∞ (fun p : ℝ × E3 => coordinates p.1 p.2) := by
    apply contDiff_euclidean.2
    intro i
    refine Fin.cases (by exact contDiff_fst) (fun j => ?_) i
    simp only [coordinates, WithLp.ofLp_toLp, Fin.cons_succ]
    fun_prop
  exact h.continuous

theorem trapped (p : manifold) (hp : p∈Model.outer) (q : manifold) (hq : q∈Model.outer) :
    ∃ K : Set manifold, IsCompact K ∧ K ⊆ Model.outer ∧
      causalFuture metric orientation Model.outer p ∩ causalPast metric orientation Model.outer q ⊆ K := by
  obtain ⟨_, hback, _, hright, hsm, _⟩ := iso_spec
  let x₀ := spatial (iso p)
  have hreg := (iso_regular (iso p)).mp (hback hp)
  let budget := max 0 (clock q - clock p)
  obtain ⟨K, hc, h₁, h₂, htrap⟩ := optical_confinement (-unitAxis) unitAxis x₀ hreg.1 hreg.2
    budget (le_max_left _ _)
  let box := (Icc (clock p) (clock q)) ×ˢ (insert x₀ K)
  let ψ : ℝ × E3 → manifold := fun u => Model.chart (coordinates u.1 u.2)
  have hcomp : IsCompact box := isCompact_Icc.prod (hc.insert _)
  have hcoords : MapsTo (fun u : ℝ × E3 => coordinates u.1 u.2) box exterior := by
    intro u hu
    rw [iso_regular, Model.spatial_coordinates]
    rcases hu.2 with eq | hm
    · rw [eq]
      exact hreg
    · exact ⟨fun e => h₁ (e ▸ hm),fun e => h₂ (e ▸ hm)⟩
  have hψ : ContinuousOn ψ box := hsm.continuousOn.comp coord_cont.continuousOn hcoords
  refine ⟨ψ '' box,hcomp.image_of_continuousOn hψ,?_,?_⟩
  · rintro _ ⟨u,hu,rfl⟩
    exact iso_spec.1 (hcoords hu)
  · intro z hz
    have htime : clock z ∈ Icc (clock p) (clock q) := ⟨future_clock hz.1, future_clock hz.2⟩
    have hzin : z ∈ Model.outer ∧ spatial (iso z) ∈ insert x₀ K := by
      rcases hz.1 with hzp | ⟨γ,h,hs,he⟩
      · rw [show z = p from hzp]
        exact ⟨hp, mem_insert _ _⟩
      · have hstart : spatial (iso (γ 0)) = x₀ := by rw [hs]
        have hopt (s : ℝ) (hs' : s ∈ Icc (0 : ℝ) 1) :
            HasDerivAt (fun t => spatial (iso (γ t))) (spatial (isoV γ s)) s ∧
            HasDerivAt (fun t => iso (γ t) 0) (isoV γ s 0) s ∧
            spatial (iso (γ s)) ≠ -unitAxis ∧ spatial (iso (γ s)) ≠ unitAxis ∧
            (1 + 1 / ‖spatial (iso (γ s)) - (-unitAxis)‖ + 1 / ‖spatial (iso (γ s)) - unitAxis‖)^2 *
              ‖spatial (isoV γ s)‖ ≤ isoV γ s 0 := by
          obtain ⟨hd,hy,_,hv⟩ := lift_causal h hs'
          exact ⟨spatial_deriv hd,time_deriv hd,(iso_regular _).mp hy |>.1,(iso_regular _).mp hy |>.2,
            (optical_factor _ ▸ hv)⟩
        have htravel : iso (γ 1) 0 - iso (γ 0) 0 ≤ budget := by
          change clock (γ 1) - clock (γ 0) ≤ budget
          rw [he,hs]
          exact (sub_le_sub_right htime.2 _).trans (le_max_right _ _)
        have hend := htrap (fun s => spatial (iso (γ s))) (fun s => spatial (isoV γ s))
          (fun s => iso (γ s) 0) (fun s => isoV γ s 0) hstart hopt 1 (right_mem_Icc.mpr zero_le_one) htravel
        refine ⟨he ▸ (h.2 1 (right_mem_Icc.mpr zero_le_one)).1, Or.inr ?_⟩
        simpa only [he] using hend
    refine ⟨(clock z,spatial (iso z)),⟨htime,hzin.2⟩,?_⟩
    change Model.chart (coordinates (iso z 0) (spatial (iso z))) = z
    rw [join_coords, hright hzin.1]
end
end NoHair.TwoCentre.Model.Signals

open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Cartesian _root_.NoHair.TwoCentre.Model
open NoHair NoHair.TwoCentre NoHair.TwoCentre.Cartesian NoHair.TwoCentre.Model Set Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace
namespace NoHair.TwoCentre.Model.CausalAtlas
open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Model
open Signals StaticCausality
noncomputable section
set_option backward.isDefEq.respectTransparency false

def eTime : VecField StaticCausality.U := fun _ => coordBasis 0
theorem mono_time (x : U) (v : E4) : G x v (eTime x) = -(v 0)/harmonicPotential x.val^2 := by
  rw [StaticCausality.metric_formula x v (eTime x)]
  simp (config:={decide:=true}) [eTime,coordBasis]
theorem eTime_oriented : IsTimeOrientation G eTime := by
  constructor
  · apply continuous_iff_continuousAt.mpr;intro z
    apply (FiberBundle.continuousAt_section E4 z).2
    have he (x : U) : (trivializationAt E4 (TangentSpace 𝓘(ℝ,E4)) z
        (⟨x,eTime x⟩ : TangentBundle 𝓘(ℝ,E4) U)).2 = coordBasis 0 := by
      change tangentCoordChange 𝓘(ℝ,E4) x z x (coordBasis 0) = _
      have same : achart E4 z = achart E4 x := by rfl
      unfold tangentCoordChange;rw [same]
      exact (tangentBundleCore 𝓘(ℝ,E4) U).coordChange_self (achart E4 x) x (mem_achart_source E4 x) _
    simp_rw [he];exact continuousAt_const
  · intro x;rw [mono_time x (eTime x)]
    have hu := Signals.Upos x.val
    change -(timeComponent (eTime x)) / harmonicPotential x.val^2 < 0
    have hn : timeComponent (eTime x) = 1 := by simp [timeComponent,eTime,coordBasis]
    rw [hn];exact div_neg_of_neg_of_pos (by norm_num) (sq_pos_of_pos hu)

def forward (x : U) := Model.chart x.val
def back (z : manifold) : U := by
  classical
  exact if h : iso z∈exterior then ⟨iso z,h⟩ else ⟨axis 0,by change axis 0 ∈ exterior;norm_num [exterior,axis,squaredDistance,Set.mem_setOf_eq] <;> positivity⟩
theorem back_coe {z : manifold} (hz : z∈Model.outer) : ((back z : U) : E4) = iso z := by
  classical
  unfold back
  simp only [dif_pos (iso_spec.2.1 hz)]
theorem right_inv {z : manifold} (hz : z∈Model.outer) : forward (back z)=z := by
  unfold forward;rw [back_coe hz];exact iso_spec.2.2.2.1 hz
theorem left_inv (x : U) : back (forward x)=x := by
  apply Subtype.ext;exact (back_coe (z:=forward x) (iso_spec.1 x.property)).trans (iso_spec.2.2.1 x.property)

theorem forward_smooth : ContMDiff I4 I4 ∞ forward := by
  intro x
  have h := ((iso_spec.2.2.2.2.1 x.val x.property).contMDiffAt (exterior_isOpen.mem_nhds x.property))
  exact h.comp x (contMDiff_subtype_val.contMDiffAt)
theorem back_smooth (z : manifold) (hz : z∈Model.outer) : ContMDiffAt I4 I4 ∞ back z := by
  apply (ContMDiffAt.subtypeVal_comp_iff U back z).1
  apply ((iso_spec.2.2.2.2.2 z hz).contMDiffAt (outer_open.mem_nhds hz)).congr_of_eventuallyEq
  exact Filter.mem_of_superset (outer_open.mem_nhds hz) (fun y hy => back_coe hy)
theorem forward_der (x:U) : (mfderiv I4 I4 forward x : E4 →L[ℝ] E4) = L x.val := by
  have hf := ((iso_spec.2.2.2.2.1 x.val x.property).contMDiffAt (exterior_isOpen.mem_nhds x.property)).mdifferentiableAt (by simp)
  change mfderiv I4 I4 (Model.chart ∘ (Subtype.val : U → E4)) x = _
  have hv : mfderiv I4 I4 (Subtype.val : U → E4) x = ContinuousLinearMap.id ℝ E4 := mfderiv_extChartAt_self (I:=I4) (x:=x)
  rw [mfderiv_comp _ hf (contMDiff_subtype_val.mdifferentiableAt (n:=(1:ℕ∞ω)) one_ne_zero),hv]
  rfl

theorem isometric (x:U) (v w:E4) : metric (forward x) (L x.val v) (L x.val w)=G x v w := by
  exact (Signals.metric_pullback x.property v w).trans ((by rw [Curves.spatial_inner] : _ = _).trans (StaticCausality.metric_formula x v w).symm)

theorem causal_iff (x:U) (v:E4) :
    IsFutureCausal metric orientation (forward x) (L x.val v) ↔ IsFutureCausal G eTime x v := by
  have hu := Signals.Upos x.val
  constructor
  · intro h
    have hn : v≠0 := fun he => by have hv := h.1;rw [he,map_zero] at hv;exact hv rfl
    refine ⟨hn, (isometric x v v).symm.trans_le h.2.1,?_⟩
    rw [mono_time x v];exact div_neg_of_neg_of_pos (neg_lt_zero.mpr (optical_future x.property v h).1) (sq_pos_of_pos hu)
  · intro h
    have hv : 0<v 0 := by
      have hi := h.2.2
      change G x v (eTime x)<0 at hi
      have hn := (mono_time x v).symm.trans_lt hi
      by_contra! he;exact (not_lt_of_ge (div_nonneg (neg_nonneg.mpr he) (sq_nonneg _))) hn
    obtain ⟨w,hw⟩ := L_onto x.property (orientation (forward x))
    have hww : G x w w<0 := by
      have hh := (isometric x w w).symm
      rw [hw] at hh
      exact hh.trans_lt (stationary_geometry.2.2.2.2.1.2 (forward x))
    have ht : L x.val (eTime x)=coordBasis 0 := chart_time x.property
    have hpair : G x w (eTime x)<0 := by
      have he := (isometric x (eTime x) w).symm
      rw [hw,ht] at he
      exact (StaticCausality.field_sym x.property w (eTime x)).trans (he) |>.trans_lt
        (time_orientation_pair (forward x) (iso_spec.1 x.property))
    have hwpos : 0 < timeComponent w := by
      have hn := (mono_time x w).symm.trans_lt hpair
      by_contra! he;exact (not_lt_of_ge (div_nonneg (neg_nonneg.mpr he) (sq_nonneg _))) hn
    have orient : metric (forward x) (L x.val v) (orientation (forward x)) < 0 := by
      have he := isometric x v w
      rw [hw] at he
      exact he.trans_lt (StaticCausality.cone_pair_negative x.property h.2.1 hww (mul_pos hv hwpos))
    refine ⟨?_,(isometric x v v).trans_le h.2.1,orient⟩
    intro he;rw [he,map_zero] at orient;exact (lt_irrefl (0:ℝ)) orient

set_option backward.isDefEq.respectTransparency false in
theorem map_future {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [ChartedSpace E4 X] [ChartedSpace E4 Y]
    [IsManifold I4 ∞ X] [IsManifold I4 ∞ Y] {A : Set X} {B : Set Y} (hA : IsOpen A)
    {g : BilinField X} {G' : BilinField Y} {T : VecField X} {T' : VecField Y}
    (f : X→Y) (hm : MapsTo f A B) (hs : ∀ x ∈ A, ContMDiffAt I4 I4 ∞ f x)
    (hd : ∀ x ∈ A, ∀ v, IsFutureCausal g T x v → IsFutureCausal G' T' (f x) (mfderiv I4 I4 f x v))
    {p q : X} (h : q∈causalFuture g T A p) : f q∈causalFuture G' T' B (f p) := by
  rcases h with e|⟨γ,hγ,h0,h1⟩
  · exact Or.inl (congrArg f (mem_singleton_iff.mp e))
  let V := γ ⁻¹' A
  have hV : IsOpen V := hA.preimage hγ.1.continuous
  obtain ⟨b,hb,hbV,hbe⟩ := StaticCausality.fit_clock hV zero_lt_one (fun t ht => (hγ.2 t ht).1)
  let c := f ∘ γ ∘ b
  have hbM := hb.contMDiff
  have sm : ContMDiff 𝓘(ℝ,ℝ) I4 1 c := by
    intro t
    exact ((hs _ (hbV t)).of_le (show (1:ℕ∞ω)≤∞ by simp)).comp t ((hγ.1.comp hbM).contMDiffAt)
  have ev (t : ℝ) (ht:t∈J) : c =ᶠ[𝓝 t] (f ∘ γ) := (hbe t ht).fun_comp (f ∘ γ)
  refine Or.inr ⟨c,⟨sm,?_⟩, (ev 0 (left_mem_Icc.mpr zero_le_one)).self_of_nhds.trans (congrArg f h0),
      (ev 1 (right_mem_Icc.mpr zero_le_one)).self_of_nhds.trans (congrArg f h1)⟩
  intro t ht
  have ec := (ev t ht).self_of_nhds
  have dt : (velocity c t : E4) = mfderiv I4 I4 f (γ t) (velocity γ t) := by
    unfold velocity
    rw [(ev t ht).mfderiv_eq, mfderiv_comp t ((hs _ (hγ.2 t ht).1).mdifferentiableAt (by simp)) (hγ.1.mdifferentiableAt (by simp))]
    rfl
  exact ⟨ec ▸ hm (hγ.2 t ht).1, by change IsFutureCausal G' T' (c t) (velocity c t : E4);rw [dt,ec];exact hd _ (hγ.2 t ht).1 _ (hγ.2 t ht).2⟩

theorem forward_future {p q : U} (h : q∈causalFuture G eTime D p) :
    forward q ∈ causalFuture metric orientation Model.outer (forward p) := by
  apply map_future (hA:=openS.preimage continuous_subtype_val) forward (fun x _ => iso_spec.1 x.property)
      (fun x _ => forward_smooth.contMDiffAt) _ h
  intro x _ v hv
  have e : (mfderiv I4 I4 forward x v : E4)=L x.val v := DFunLike.congr_fun (forward_der x) v
  exact e ▸ (causal_iff x v).2 hv

theorem backward_future {p q : manifold} (h : q∈causalFuture metric orientation Model.outer p) :
    back q ∈ causalFuture G eTime D (back p) := by
  apply map_future (hA:=outer_open) back (fun x _ => (back x).property) back_smooth _ h
  intro x hx v hv
  let a := back x
  let w := mfderiv I4 I4 back x v
  have he : (forward ∘ back)=ᶠ[𝓝 x] id := Filter.mem_of_superset (outer_open.mem_nhds hx) (fun z hz => right_inv hz)
  have hd := he.mfderiv_eq (I:=I4) (I':=I4)
  rw [mfderiv_comp _ (forward_smooth.mdifferentiableAt (by simp)) ((back_smooth x hx).mdifferentiableAt (by simp)),mfderiv_id] at hd
  have hw : L a.val w = v := (DFunLike.congr_fun (forward_der a) w).symm.trans (DFunLike.congr_fun hd v)
  apply (causal_iff a w).mp
  rw [hw,show forward a=x from right_inv hx];exact hv

end
end NoHair.TwoCentre.Model.CausalAtlas

open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Model
open NoHair NoHair.TwoCentre NoHair.TwoCentre.Model Set
open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Model
open NoHair.TwoCentre.StaticCausality NoHair.TwoCentre.Model.CausalAtlas
open scoped ContDiff Manifold
namespace NoHair.TwoCentre.Model.CausalAtlas
open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Model
noncomputable section

theorem closed (p : manifold) (hp : p∈Model.outer) (q : manifold) (hq : q∈Model.outer) :
    IsClosed (causalFuture metric orientation Model.outer p ∩ causalPast metric orientation Model.outer q) := by
  let A := causalFuture metric orientation Model.outer p ∩ causalPast metric orientation Model.outer q
  let B := causalFuture G eTime D (back p) ∩ causalPast G eTime D (back q)
  have hmap : MapsTo forward B A := by
    intro z hz
    have h1 := forward_future hz.1
    have h2 := forward_future hz.2
    rw [right_inv hp] at h1;rw [right_inv hq] at h2
    exact ⟨h1,h2⟩
  obtain ⟨K,hK,hKD,hAK⟩ := Signals.trapped p hp q hq
  have hb : ContinuousOn back K := fun z hz => (back_smooth z (hKD hz)).continuousAt.continuousWithinAt
  have hKB : B ⊆ back '' K := by
    intro z hz;exact ⟨forward z,hAK (hmap hz),left_inv z⟩
  let container : TopologicalSpace.Compacts StaticCausality.U := ⟨back '' K,hK.image_of_continuousOn hb⟩
  have hc : IsCompact B := (StaticCausality.causalIntervalIn eTime eTime_oriented (back p) (back q) container hKB).isCompact
  have himg : forward '' B = A := by
    apply subset_antisymm (image_subset_iff.mpr hmap)
    intro z hz
    exact ⟨back z,⟨backward_future hz.1,backward_future hz.2⟩,right_inv (hKD (hAK hz))⟩
  change IsClosed A;rw [←himg];exact (hc.image forward_smooth.continuous).isClosed

end
end NoHair.TwoCentre.Model.CausalAtlas
open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Model
open NoHair NoHair.TwoCentre.Model Set
theorem checkedResult : ∀ p ∈ outer, ∀ q ∈ outer,
    IsClosed (causalFuture metric orientation outer p ∩ causalPast metric orientation outer q) :=
  fun p hp q hq => CausalAtlas.closed p hp q hq
end ElectrovacProof031

alias NoHair.TwoCentre.Model.closed_causal_diamonds := ElectrovacProof031.checkedResult


namespace ElectrovacProof032

open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Cartesian _root_.NoHair.TwoCentre.Model
open NoHair NoHair.TwoCentre NoHair.TwoCentre.Cartesian NoHair.TwoCentre.Model Set Topology
open scoped ContDiff Manifold RealInnerProductSpace

namespace NoHair.TwoCentre.Model.Curves
open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Model

noncomputable section

export _root_.ElectrovacProof003.NoHair.TwoCentre.Model.Curves (radialSpeed)

export _root_.ElectrovacProof003.NoHair.TwoCentre.Model.Curves (spatial_inner)

export _root_.ElectrovacProof003.NoHair.TwoCentre.Model.Curves (radialSpeed_coords)

export _root_.ElectrovacProof003.NoHair.TwoCentre.Model.Curves (metric_eval)

export _root_.ElectrovacProof003.NoHair.TwoCentre.Model.Curves (angular_unit)

end
end NoHair.TwoCentre.Model.Curves


open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Cartesian _root_.NoHair.TwoCentre.Model
open NoHair NoHair.TwoCentre NoHair.TwoCentre.Cartesian NoHair.TwoCentre.Model Set Filter Topology
open scoped ContDiff Manifold RealInnerProductSpace BigOperators

namespace NoHair.TwoCentre.Model.Signals
open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Model

noncomputable section

export _root_.ElectrovacProof029.NoHair.TwoCentre.Model.Signals (spatial_cont)

export _root_.ElectrovacProof029.NoHair.TwoCentre.Model.Signals (outer_open)

export _root_.ElectrovacProof029.NoHair.TwoCentre.Model.Signals (outer_subset)

export _root_.ElectrovacProof029.NoHair.TwoCentre.Model.Signals (model_chart_val)

export _root_.ElectrovacProof029.NoHair.TwoCentre.Model.Signals (model_chart_diffeo)

export _root_.ElectrovacProof029.NoHair.TwoCentre.Model.Signals (exterior_isOpen)

export _root_.ElectrovacProof029.NoHair.TwoCentre.Model.Signals (L)

export _root_.ElectrovacProof029.NoHair.TwoCentre.Model.Signals (L_onto)

export _root_.ElectrovacProof029.NoHair.TwoCentre.Model.Signals (Upos)

export _root_.ElectrovacProof029.NoHair.TwoCentre.Model.Signals (metric_pullback)

export _root_.ElectrovacProof029.NoHair.TwoCentre.Model.Signals (chart_time)

export _root_.ElectrovacProof029.NoHair.TwoCentre.Model.Signals (time_orientation_pair)

export _root_.ElectrovacProof031.NoHair.TwoCentre.Model.Signals (iso)

export _root_.ElectrovacProof031.NoHair.TwoCentre.Model.Signals (iso_spec)

export _root_.ElectrovacProof031.NoHair.TwoCentre.Model.Signals (optical_future)

export _root_.ElectrovacProof031.NoHair.TwoCentre.Model.Signals (isoV)

set_option backward.isDefEq.respectTransparency false in
export _root_.ElectrovacProof031.NoHair.TwoCentre.Model.Signals (lift_causal)

export _root_.ElectrovacProof031.NoHair.TwoCentre.Model.Signals (clock)

export _root_.ElectrovacProof031.NoHair.TwoCentre.Model.Signals (interval_strict)

export _root_.ElectrovacProof031.NoHair.TwoCentre.Model.Signals (future_clock)

export _root_.ElectrovacProof031.NoHair.TwoCentre.Model.Signals (spatial_dist)

export _root_.ElectrovacProof031.NoHair.TwoCentre.Model.Signals (iso_regular)

export _root_.ElectrovacProof031.NoHair.TwoCentre.Model.Signals (optical_factor)

export _root_.ElectrovacProof031.NoHair.TwoCentre.Model.Signals (spatial_deriv)

export _root_.ElectrovacProof031.NoHair.TwoCentre.Model.Signals (time_deriv)

export _root_.ElectrovacProof031.NoHair.TwoCentre.Model.Signals (join_coords)

export _root_.ElectrovacProof031.NoHair.TwoCentre.Model.Signals (coord_cont)

theorem hyperbolicity_from_closed
    (hcl : ∀ p ∈ Model.outer, ∀ q ∈ Model.outer,
      IsClosed (causalFuture metric orientation Model.outer p ∩ causalPast metric orientation Model.outer q)) :
    IsGloballyHyperbolicOn metric orientation Model.outer := by
  constructor
  · rintro p _ ⟨γ,h,hs,he⟩
    have lt := interval_strict h (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one) zero_lt_one
    simp [hs,he] at lt
  · intro p hp q hq
    obtain ⟨_, hback, _, hright, hsm, _⟩ := iso_spec
    let x₀ := spatial (iso p)
    have hreg := (iso_regular (iso p)).mp (hback hp)
    let budget := max 0 (clock q - clock p)
    obtain ⟨K, hc, h₁, h₂, htrap⟩ := optical_confinement (-unitAxis) unitAxis x₀ hreg.1 hreg.2
      budget (le_max_left _ _)
    let box := (Icc (clock p) (clock q)) ×ˢ (insert x₀ K)
    let ψ : ℝ × E3 → manifold := fun u => Model.chart (coordinates u.1 u.2)
    have hcomp : IsCompact box := isCompact_Icc.prod (hc.insert _)
    have hcoords : MapsTo (fun u : ℝ × E3 => coordinates u.1 u.2) box exterior := by
      intro u hu
      rw [iso_regular, Model.spatial_coordinates]
      rcases hu.2 with eq | hm
      · rw [eq]
        exact hreg
      · exact ⟨fun e => h₁ (e ▸ hm),fun e => h₂ (e ▸ hm)⟩
    have hψ : ContinuousOn ψ box := hsm.continuousOn.comp coord_cont.continuousOn hcoords
    apply (hcomp.image_of_continuousOn hψ).of_isClosed_subset (hcl p hp q hq)
    intro z hz
    have htime : clock z ∈ Icc (clock p) (clock q) := ⟨future_clock hz.1, future_clock hz.2⟩
    have hzin : z ∈ Model.outer ∧ spatial (iso z) ∈ insert x₀ K := by
      rcases hz.1 with hzp | ⟨γ,h,hs,he⟩
      · rw [show z = p from hzp]
        exact ⟨hp, mem_insert _ _⟩
      · have hstart : spatial (iso (γ 0)) = x₀ := by rw [hs]
        have hopt (s : ℝ) (hs' : s ∈ Icc (0 : ℝ) 1) :
            HasDerivAt (fun t => spatial (iso (γ t))) (spatial (isoV γ s)) s ∧
            HasDerivAt (fun t => iso (γ t) 0) (isoV γ s 0) s ∧
            spatial (iso (γ s)) ≠ -unitAxis ∧ spatial (iso (γ s)) ≠ unitAxis ∧
            (1 + 1 / ‖spatial (iso (γ s)) - (-unitAxis)‖ + 1 / ‖spatial (iso (γ s)) - unitAxis‖)^2 *
              ‖spatial (isoV γ s)‖ ≤ isoV γ s 0 := by
          obtain ⟨hd,hy,_,hv⟩ := lift_causal h hs'
          exact ⟨spatial_deriv hd,time_deriv hd,(iso_regular _).mp hy |>.1,(iso_regular _).mp hy |>.2,
            (optical_factor _ ▸ hv)⟩
        have htravel : iso (γ 1) 0 - iso (γ 0) 0 ≤ budget := by
          change clock (γ 1) - clock (γ 0) ≤ budget
          rw [he,hs]
          exact (sub_le_sub_right htime.2 _).trans (le_max_right _ _)
        have hend := htrap (fun s => spatial (iso (γ s))) (fun s => spatial (isoV γ s))
          (fun s => iso (γ s) 0) (fun s => isoV γ s 0) hstart hopt 1 (right_mem_Icc.mpr zero_le_one) htravel
        refine ⟨he ▸ (h.2 1 (right_mem_Icc.mpr zero_le_one)).1, Or.inr ?_⟩
        simpa only [he] using hend
    refine ⟨(clock z,spatial (iso z)),⟨htime,hzin.2⟩,?_⟩
    change Model.chart (coordinates (iso z 0) (spatial (iso z))) = z
    rw [join_coords, hright hzin.1]

end
end NoHair.TwoCentre.Model.Signals

open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Model
open NoHair.TwoCentre.Model.Signals

theorem checkedResult : IsGloballyHyperbolicOn metric orientation Model.outer :=
  hyperbolicity_from_closed Model.closed_causal_diamonds
end ElectrovacProof032

alias NoHair.TwoCentre.Model.global_hyperbolicity := ElectrovacProof032.checkedResult


namespace ElectrovacProof033

/-! The Kerr–Schild derivative and index-raising calculations below are from the accepted
Prove2Me solution f8c62ec4-e576-4bf9-aa5b-a5897df2f835 (Apache 2.0). -/

open _root_.NoHair _root_.NoHair.KNE
open NoHair NoHair.KNE
open scoped BigOperators

private lemma rnField (e : ℝ) (y : E4) (hy : 0 < ksRadius 0 y) (i j : Fin 4) :
    kerrNewmanField 0 e y i j =
      FA 0 e (ksRadius 0 y) (ksNull 0 y 1) (ksNull 0 y 2) (ksNull 0 y 3) (Wf 0 y) i j := by
  have hA : ∀ k, HasCP (fun z => kerrNewmanPotential 0 e z k) y
      (fun l => dHA 0 e (ksRadius 0 y) (ksNull 0 y 1) (ksNull 0 y 2) (ksNull 0 y 3)
          (Wf 0 y) l * ksNull 0 y k
        + e * ksRadius 0 y ^ 3 / (ksRadius 0 y ^ 4 + (0 : ℝ) ^ 2 * y 3 ^ 2)
          * dKt 0 (ksRadius 0 y) (ksNull 0 y 1) (ksNull 0 y 2) (ksNull 0 y 3)
            (Wf 0 y) k l) :=
    fun k => (hasCP_H 0 e y hy).mul (hasCP_K 0 y hy k)
  have hpot : e * ksRadius 0 y ^ 3 / (ksRadius 0 y ^ 4 + (0 : ℝ) ^ 2 * y 3 ^ 2) =
      HA 0 e (ksRadius 0 y) (Wf 0 y) := by
    simp [HA, Wf]
    field_simp [hy.ne']
  unfold kerrNewmanField
  rw [(hA j).eq i, (hA i).eq j, hpot,
    ← fS 0 e _ _ _ _ _ (ks_rel 0 y hy) (ks_W 0 y hy) i j]
  simp only [FS, Kv, ← ksNull_eq_Kv 0 y]

private lemma rnRaisedField (m e : ℝ) (y : E4) (hy : 0 < ksRadius 0 y) (i j : Fin 4) :
    raiseBoth (kerrNewmanMetric m 0 e) (kerrNewmanField 0 e) y i j =
      FupA 0 m e (ksRadius 0 y) (ksNull 0 y 1) (ksNull 0 y 2) (ksNull 0 y 3)
        (Wf 0 y) i j := by
  unfold raiseBoth
  simp only [invMetric_eq m 0 e y hy, Matrix.of_apply, rnField e y hy]
  exact fU 0 m e _ _ _ _ _ (ks_rel 0 y hy) (ks_W 0 y hy) i j

private lemma leviCivita_perm (p : Equiv.Perm (Fin 4)) :
    leviCivita (p 0) (p 1) (p 2) (p 3) = ((Equiv.Perm.sign p : ℤ) : ℝ) := by
  have hf : ![p 0, p 1, p 2, p 3] = (p : Fin 4 → Fin 4) := by
    funext i
    fin_cases i <;> rfl
  have hp : Equiv.ofBijective (p : Fin 4 → Fin 4) p.bijective = p := by
    ext i
    rfl
  simp [leviCivita, hf, hp]

private theorem epsilon_repeat (a b c d s t : Fin 4) (hne : s ≠ t)
    (h : (![a,b,c,d] : Fin 4 → Fin 4) s = ![a,b,c,d] t) : leviCivita a b c d = 0 := by
  unfold leviCivita
  exact dif_neg (fun hbij => hne (hbij.1 h))

private theorem epsAC (a b c : Fin 4) : leviCivita a b a c = 0 :=
  epsilon_repeat a b a c 0 2 (by decide) rfl
private theorem epsAD (a b c : Fin 4) : leviCivita a b c a = 0 :=
  epsilon_repeat a b c a 0 3 (by decide) rfl
private theorem epsBC (a b c : Fin 4) : leviCivita a b b c = 0 :=
  epsilon_repeat a b b c 1 2 (by decide) rfl
private theorem epsBD (a b c : Fin 4) : leviCivita a b c b = 0 :=
  epsilon_repeat a b c b 1 3 (by decide) rfl

private lemma oriented_eps (p : Equiv.Perm (Fin 4)) (hp : Equiv.Perm.sign p = 1) :
    leviCivita (p 0) (p 1) (p 2) (p 3) = 1 ∧ leviCivita (p 0) (p 1) (p 3) (p 2) = -1 := by
  constructor
  · simp [leviCivita_perm, hp]
  · let q := p * Equiv.swap (2 : Fin 4) 3
    have h := leviCivita_perm q
    have h0 : Equiv.swap (2 : Fin 4) 3 0 = 0 := by decide
    have h1 : Equiv.swap (2 : Fin 4) 3 1 = 1 := by decide
    simpa [q, hp, Equiv.Perm.mul_apply, h0, h1] using h

private lemma pair_forces_zero (β x : ℝ)
    (hE : Real.cos β = 0 ∨ x = 0) (hB : Real.sin β = 0 ∨ x = 0) : x = 0 := by
  by_contra hx
  have hh := Real.sin_sq_add_cos_sq β
  norm_num [hE.resolve_right hx, hB.resolve_right hx] at hh

/-- At any point of strictly positive Reissner–Nordström radius, even a constant duality
rotation can make the Maxwell field vanish only when the charge is zero. -/
theorem NoHair.rn_charge_zero_at_field_zero (m e β : ℝ) (y : E4) (hy : 0 < ksRadius 0 y)
    (hzero : Real.cos β • kerrNewmanField 0 e y +
      Real.sin β • hodgeDual (kerrNewmanMetric m 0 e y) (kerrNewmanField 0 e y) = 0) : e = 0 := by
  let r := ksRadius 0 y
  let W := Wf 0 y
  let n := ksNull 0 y
  let u := r ^ 4 * W ^ 3 * e
  let vol := Real.sqrt |(kerrNewmanMetric m 0 e y).det|
  have hE (i j : Fin 4) :
      kerrNewmanField 0 e y i j = FA 0 e r (n 1) (n 2) (n 3) W i j := rnField e y hy i j
  have hB (i j : Fin 4) : hodgeDual (kerrNewmanMetric m 0 e y) (kerrNewmanField 0 e y) i j =
      (1 / 2 : ℝ) * vol * ((leviCivita i j 1 0 - leviCivita i j 0 1) * (u * n 1) +
        (leviCivita i j 2 0 - leviCivita i j 0 2) * (u * n 2) +
        (leviCivita i j 3 0 - leviCivita i j 0 3) * (u * n 3)) := by
    change (1 / 2 : ℝ) * vol * (∑ k, ∑ l, leviCivita i j k l *
        raiseBoth (kerrNewmanMetric m 0 e) (kerrNewmanField 0 e) y k l) = _
    have hup (k l : Fin 4) : raiseBoth (kerrNewmanMetric m 0 e) (kerrNewmanField 0 e) y k l =
        FupA 0 m e r (n 1) (n 2) (n 3) W k l := rnRaisedField m e y hy k l
    simp only [hup, Fin.sum_univ_four]
    simp [FupA, Fu01, Fu02, Fu03, Fu12, Fu13, Fu23, u]
    left
    ring
  have hcomponent (i j : Fin 4) : Real.cos β * FA 0 e r (n 1) (n 2) (n 3) W i j +
      Real.sin β * ((1 / 2 : ℝ) * vol * ((leviCivita i j 1 0 - leviCivita i j 0 1) * (u * n 1) +
        (leviCivita i j 2 0 - leviCivita i j 0 2) * (u * n 2) +
        (leviCivita i j 3 0 - leviCivita i j 0 3) * (u * n 3))) = 0 := by
    rw [← hE i j, ← hB i j]
    exact congrArg (fun A : Matrix (Fin 4) (Fin 4) ℝ => A i j) hzero
  have h231 : leviCivita 2 3 0 1 = 1 ∧ leviCivita 2 3 1 0 = -1 :=
    oriented_eps (Equiv.swap 0 2 * Equiv.swap 1 3) (by simp)
  have h312 : leviCivita 3 1 0 2 = 1 ∧ leviCivita 3 1 2 0 = -1 :=
    oriented_eps (Equiv.swap 0 2 * Equiv.swap 0 3) (by simp)
  have h123 : leviCivita 1 2 0 3 = 1 ∧ leviCivita 1 2 3 0 = -1 :=
    oriented_eps (Equiv.swap 0 1 * Equiv.swap 1 2) (by simp)
  have hdet : (kerrNewmanMetric m 0 e y).det ≠ 0 :=
    Matrix.det_ne_zero_of_right_inverse (mul_inv_KS (ksProfile m 0 e y) _ (ks_null 0 y hy))
  have hv : vol ≠ 0 := (Real.sqrt_pos.2 (abs_pos.mpr hdet)).ne'
  by_contra he
  have hW : 0 < W := by
    simp only [W, Wf, zero_pow (by decide : 2 ≠ 0), zero_mul, add_zero]
    exact one_div_pos.mpr (sq_pos_of_pos hy)
  have hu : u ≠ 0 := mul_ne_zero (mul_ne_zero (pow_ne_zero 4 hy.ne') (pow_ne_zero 3 hW.ne')) he
  have hrel : n 1 ^ 2 + n 2 ^ 2 + n 3 ^ 2 = 1 := ks_rel 0 y hy
  have E1 := hcomponent 0 1
  have E2 := hcomponent 0 2
  have E3 := hcomponent 0 3
  have B1 := hcomponent 2 3
  have B2 := hcomponent 3 1
  have B3 := hcomponent 1 2
  have hr : r ≠ 0 := hy.ne'
  simp [FA, Fc01, Fc02, Fc03, Fc12, Fc13, Fc23, epsAC, epsAD, epsBC, epsBD,
    h231.1, h231.2, h312.1, h312.2, h123.1, h123.2] at E1 E2 E3 B1 B2 B3
  norm_num [hr, hW.ne', he, hv, hu] at E1 E2 E3 B1 B2 B3
  norm_num [pair_forces_zero β _ E1 B1, pair_forces_zero β _ E2 B2,
    pair_forces_zero β _ E3 B3] at hrel

open scoped ContDiff Manifold Topology
open Set Filter

private theorem bilinear_zero_of_basis_pullback (B : E4 →L[ℝ] E4 →L[ℝ] ℝ)
    (L : E4 →L[ℝ] E4) (hL : Function.Surjective L)
    (h : ∀ i j, B (L (coordBasis i)) (L (coordBasis j)) = 0) : B = 0 := by
  have hexpand (x : E4) : ∑ i, x i • coordBasis i = x := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply, coordBasis] using
      (EuclideanSpace.basisFun (Fin 4) ℝ).sum_repr x
  ext v w
  obtain ⟨a, rfl⟩ := hL v
  obtain ⟨c, rfl⟩ := hL w
  calc
    B (L a) (L c) = B (L (∑ i, a i • coordBasis i)) (L (∑ i, c i • coordBasis i)) := by
      rw [hexpand, hexpand]
    _ = 0 := by simp [map_sum, map_smul, sum_apply, smul_apply, h]

private theorem chart_derivative_surjective {M : Type*} [TopologicalSpace M] [ChartedSpace E4 M]
    [IsManifold 𝓘(ℝ, E4) ∞ M] {U : Set E4} {D : Set M} {Ψ : E4 → M}
    (hU : IsOpen U) (hD : IsOpen D) (h : IsDiffeoOnto Ψ U D) (y : E4) (hy : y ∈ U) :
    Function.Surjective (mfderiv 𝓘(ℝ, E4) 𝓘(ℝ, E4) Ψ y) := by
  obtain ⟨χ, hmap, hinv, hleft, hright, hs, ht⟩ := h
  have hx := hmap hy
  have hcomp : (Ψ ∘ χ) =ᶠ[𝓝 (Ψ y)] id :=
    Filter.mem_of_superset (hD.mem_nhds hx) (fun _ hz => hright hz)
  have hf := ((hs _ (hinv hx)).contMDiffAt (hU.mem_nhds (hinv hx))).mdifferentiableAt (by simp)
  have hi := ((ht _ hx).contMDiffAt (hD.mem_nhds hx)).mdifferentiableAt (by simp)
  have hder : mfderiv 𝓘(ℝ, E4) 𝓘(ℝ, E4) (Ψ ∘ χ) (Ψ y) =
      ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ, E4) (Ψ y)) := hcomp.mfderiv_eq.trans mfderiv_id
  rw [mfderiv_comp _ hf hi, hleft hy] at hder
  intro v
  refine ⟨mfderiv 𝓘(ℝ, E4) 𝓘(ℝ, E4) χ (Ψ y) v, ?_⟩
  exact DFunLike.congr_fun hder v

/-- A diffeomorphism between open regions preserves and reflects tensor zeros. -/
theorem NoHair.pullbackCoeffs_zero_iff_on_chart {M : Type*}
    [TopologicalSpace M] [ChartedSpace E4 M] [IsManifold 𝓘(ℝ, E4) ∞ M]
    (F : BilinField M) {U : Set E4} {D : Set M} {Ψ : E4 → M}
    (hU : IsOpen U) (hD : IsOpen D) (h : IsDiffeoOnto Ψ U D) {y : E4} (hy : y ∈ U) :
    pullbackCoeffs F Ψ y = 0 ↔ F (Ψ y) = 0 := by
  constructor
  · intro hp
    apply bilinear_zero_of_basis_pullback _ _ (chart_derivative_surjective hU hD h y hy)
    intro i j
    exact congrArg (fun A : Matrix (Fin 4) (Fin 4) ℝ => A i j) hp
  · intro hz
    ext i j
    exact DFunLike.congr_fun (DFunLike.congr_fun hz _) _

/-- The zero set of the Faraday tensor on any open Reissner–Nordström exterior
is either empty or the entire exterior, including after the allowed duality rotation. -/
theorem NoHair.not_rn_doc_of_mixed_field_zeros {M : Type*}
    [TopologicalSpace M] [ChartedSpace E4 M] [IsManifold 𝓘(ℝ, E4) ∞ M]
    (g F : BilinField M) (D : Set M) (hD : IsOpen D)
    (hz : ∃ x ∈ D, F x = 0) (hnz : ∃ x ∈ D, F x ≠ 0) :
    ¬ ∃ m e : ℝ, IsKerrNewmanBlackHoleParams m 0 e ∧ IsKerrNewmanDOC g F D m 0 e := by
  rintro ⟨m, e, hp, β, Ψ, hdif, hfields⟩
  have hex := hdif
  obtain ⟨χ, _, hinv, _, hright, _, _⟩ := hex
  obtain ⟨x, hx, hFx⟩ := hz
  have hxy := hinv hx
  have hpos : 0 < ksRadius 0 (χ x) :=
    lt_trans (add_pos_of_pos_of_nonneg hp.1 (Real.sqrt_nonneg _)) hxy
  have hU : IsOpen (kerrNewmanDOC m 0 e) := isOpen_lt continuous_const (continuous_ksRadius 0)
  have hF : F (Ψ (χ x)) = 0 := (congrArg (fun z : M => F z = 0) (hright hx)).mpr hFx
  have hzero := (pullbackCoeffs_zero_iff_on_chart F hU hD hdif hxy).mpr hF
  have he := rn_charge_zero_at_field_zero m e β (χ x) hpos ((hfields _ hxy).2.symm.trans hzero)
  subst e
  obtain ⟨z, hz, hFz⟩ := hnz
  have hzy := hinv hz
  have hzeroF : kerrNewmanField 0 0 (χ z) = 0 := by
    ext i j
    simp [kerrNewmanField, kerrNewmanPotential, coordPartial]
  have hzeroStar : hodgeDual (kerrNewmanMetric m 0 0 (χ z)) 0 = 0 := by
    ext i j
    simp [hodgeDual]
  have hpull : pullbackCoeffs F Ψ (χ z) = 0 := by
    rw [(hfields _ hzy).2, hzeroF, hzeroStar, smul_zero, smul_zero, zero_add]
  have hvan := (pullbackCoeffs_zero_iff_on_chart F hU hD hdif hzy).mp hpull
  exact hFz ((congrArg (fun p : M => F p = 0) (hright hz)).mp hvan)

/-! The electrostatic potential of the equal-mass Majumdar–Papapetrou exterior, with
centres at spatial coordinates (−1,0,0) and (1,0,0). Hartle and Hawking (1972), §II,
equations (2.1)–(2.8). The Maxwell two-form in this chart is d(Φ dt). -/

open _root_.NoHair _root_.NoHair.KNE
open NoHair NoHair.KNE

namespace NoHair.TwoCentre
open _root_.NoHair _root_.NoHair.TwoCentre

noncomputable section

private lemma axis_x (a : ℝ) : axis a 1 = a := rfl
private lemma axis_y (a : ℝ) : axis a 2 = 0 := rfl
private lemma axis_z (a : ℝ) : axis a 3 = 0 := rfl

theorem sqrtCP {f : E4 → ℝ} {y : E4} {df : Fin 4 → ℝ}
    (h : HasCP f y df) (hne : f y ≠ 0) :
    HasCP (fun z => Real.sqrt (f z)) y (fun i => df i / (2 * Real.sqrt (f y))) := by
  refine ⟨h.diff.sqrt hne, ?_⟩
  intro i
  have hn : f (y + (0 : ℝ) • coordBasis i) ≠ 0 := by simpa using hne
  simpa only [zero_smul, add_zero] using (h.line i).sqrt hn

theorem inverseDistanceCP (a c : ℝ) (hac : a ≠ c) :
    HasCP (inverseDistance c) (axis a)
      (fun k => -((a - c) * coordBasis k 1) / |a - c| ^ 3) := by
  have hval : squaredDistance c (axis a) = (a - c) ^ 2 := by
    simp [squaredDistance, axis_x, axis_y, axis_z]
  have habs : |a - c| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr hac)
  have hsqrt : Real.sqrt (squaredDistance c (axis a)) = |a - c| := by
    rw [hval, Real.sqrt_sq_eq_abs]
  have hd : HasCP (squaredDistance c) (axis a) (fun k => 2 * (a - c) * coordBasis k 1) := by
    have h := ((((hasCP_coord (axis a) 1).sub (HasCP.cst c _)).pow 2).add
      ((hasCP_coord (axis a) 2).pow 2)).add ((hasCP_coord (axis a) 3).pow 2)
    apply h.congr_d
    intro k
    simp [axis_x, axis_y, axis_z]
  have hr := sqrtCP hd (hval ▸ pow_ne_zero 2 (sub_ne_zero.mpr hac))
  have h := (HasCP.cst 1 (axis a)).div hr (hsqrt ▸ habs)
  apply h.congr_d
  intro k
  dsimp only
  rw [hsqrt]
  field_simp [habs]
  ring

theorem electricPotentialCP (a : ℝ) (hl : a ≠ -1) (hr : a ≠ 1)
    (hU : harmonicPotential (axis a) ≠ 0) :
    HasCP electricPotential (axis a) (fun k =>
      -(-((a - -1) * coordBasis k 1) / |a - -1| ^ 3 +
        -((a - 1) * coordBasis k 1) / |a - 1| ^ 3) / harmonicPotential (axis a) ^ 2) := by
  have hu := ((HasCP.cst 1 (axis a)).add (inverseDistanceCP a (-1) hl)).add
    (inverseDistanceCP a 1 hr)
  apply ((HasCP.cst 1 (axis a)).div hu hU).congr_d
  intro k
  simp [harmonicPotential]

/-- Both points are regular exterior points of the punctured spatial domain. -/
theorem field_zero_and_nonzero : field (axis 0) = 0 ∧ field (axis 2) 0 1 = -(10 / 49 : ℝ) := by
  have val0 : harmonicPotential (axis 0) = 3 := by
    norm_num [harmonicPotential, inverseDistance, squaredDistance, axis_x, axis_y, axis_z]
  have val2 : harmonicPotential (axis 2) = 7 / 3 := by
    norm_num [harmonicPotential, inverseDistance, squaredDistance, axis_x, axis_y, axis_z]
  have h0 := electricPotentialCP 0 (by norm_num) (by norm_num) (val0 ▸ by norm_num)
  have h2 := electricPotentialCP 2 (by norm_num) (by norm_num) (val2 ▸ by norm_num)
  have hzero (k) : coordPartial electricPotential k (axis 0) = 0 := by
    rw [h0.eq k, val0]
    norm_num
  refine ⟨?_, ?_⟩
  · ext i j
    simp [field, hzero]
  · simp only [field, show (1 : Fin 4) ≠ 0 by decide, if_false, if_true, zero_sub]
    rw [h2.eq 1, val2]
    norm_num [coordBasis, PiLp.single_apply]

end
end NoHair.TwoCentre

open scoped ContDiff Manifold
open _root_.NoHair
open Set NoHair

namespace NoHair.TwoCentre
open _root_.NoHair _root_.NoHair.TwoCentre

theorem isOpen_exterior : IsOpen exterior := by
  have h (c : ℝ) : Continuous (squaredDistance c) := by unfold squaredDistance; fun_prop
  exact (isOpen_lt (continuous_const (y := (0 : ℝ))) (h (-1))).inter
    (isOpen_lt continuous_const (h 1))

theorem axis_mem_exterior (a : ℝ) (hl : a ≠ -1) (hr : a ≠ 1) : axis a ∈ exterior := by
  have hx : (axis a) 1 = a := rfl
  have hy : (axis a) 2 = 0 := rfl
  have hz : (axis a) 3 = 0 := rfl
  simpa [exterior, squaredDistance, hx, hy, hz] using
    And.intro (sq_pos_of_ne_zero (sub_ne_zero.mpr hl)) (sq_pos_of_ne_zero (sub_ne_zero.mpr hr))

end NoHair.TwoCentre

open _root_.NoHair _root_.NoHair.TwoCentre
open NoHair NoHair.TwoCentre Set
open scoped ContDiff Manifold

theorem checkedResult {M : Type*} [TopologicalSpace M] [ChartedSpace E4 M]
    [IsManifold 𝓘(ℝ, E4) ∞ M] (g F : BilinField M) (D : Set M)
    (hD : IsOpen D) (Ψ : E4 → M) (hΨ : IsDiffeoOnto Ψ exterior D)
    (hfield : ∀ y ∈ exterior, pullbackCoeffs F Ψ y = field y) :
    ¬ ∃ m e : ℝ, IsKerrNewmanBlackHoleParams m 0 e ∧ IsKerrNewmanDOC g F D m 0 e := by
  have h0 := axis_mem_exterior 0 (by norm_num) (by norm_num)
  have h2 := axis_mem_exterior 2 (by norm_num) (by norm_num)
  have hex := hΨ
  obtain ⟨_, hmap, _⟩ := hex
  apply not_rn_doc_of_mixed_field_zeros g F D hD
  · refine ⟨Ψ (axis 0), hmap h0, ?_⟩
    exact (pullbackCoeffs_zero_iff_on_chart F isOpen_exterior hD hΨ h0).mp
      ((hfield _ h0).trans field_zero_and_nonzero.1)
  · refine ⟨Ψ (axis 2), hmap h2, ?_⟩
    intro hz
    have hmat := (hfield _ h2).symm.trans
      ((pullbackCoeffs_zero_iff_on_chart F isOpen_exterior hD hΨ h2).mpr hz)
    have hentry := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℝ => A 0 1) hmat
    change field (axis 2) 0 1 = 0 at hentry
    rw [field_zero_and_nonzero.2] at hentry
    norm_num at hentry

end ElectrovacProof033

alias NoHair.TwoCentre.not_israel_conclusion := ElectrovacProof033.checkedResult


namespace ElectrovacProof034

open _root_.NoHair _root_.NoHair.TwoCentre _root_.NoHair.TwoCentre.Cartesian _root_.NoHair.TwoCentre.Model
open NoHair NoHair.TwoCentre NoHair.TwoCentre.Cartesian NoHair.TwoCentre.Model Set Filter Topology
open scoped ContDiff Manifold

theorem checkedResult :
    ∃ E : AsymptoticallyFlatEnd metric faraday flow,
      IsStationaryBlackHole metric faraday orientation flow E ∧
      IsStaticOn metric flow (domainOfOuterCommunications metric orientation E.region) ∧
      ¬ ∃ m e : ℝ, IsKerrNewmanBlackHoleParams m 0 e ∧
        IsKerrNewmanDOC metric faraday (domainOfOuterCommunications metric orientation E.region) m 0 e := by
  obtain ⟨hg, hsm, hsf, htwo, htime, hflow, hstatic, hmatch⟩ := Model.stationary_geometry
  let E := TwoCentreEndConstruction.standardEnd
  have hE : E.region = Model.chart '' exteriorRegion 2 := TwoCentreEndConstruction.standardEnd_region
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
    exact not_israel_conclusion metric faraday Model.outer TwoCentreEndConstruction.outer_open Model.chart TwoCentreEndConstruction.model_chart_diffeo
      (fun y hy => (hmatch y hy).2)
end ElectrovacProof034

alias NoHair.TwoCentre.Model.one_horizon_counterexample := ElectrovacProof034.checkedResult

open scoped ContDiff Manifold BigOperators
open NoHair NoHair.TwoCentre.Model
theorem solution : ¬ (∀ {M : Type} [TopologicalSpace M] [ChartedSpace E4 M]
    [IsManifold 𝓘(ℝ, E4) ∞ M] (g F : BilinField M) (T : VecField M) (φ : ℝ → M → M)
    (E : AsymptoticallyFlatEnd g F φ) (_ : IsStationaryBlackHole g F T φ E)
    (_ : IsStaticOn g φ (domainOfOuterCommunications g T E.region)),
    ∃ m e : ℝ, IsKerrNewmanBlackHoleParams m 0 e ∧
      IsKerrNewmanDOC g F (domainOfOuterCommunications g T E.region) m 0 e) := by
  intro claim
  obtain ⟨E,hB,hS,hN⟩ := one_horizon_counterexample
  exact hN (claim metric faraday orientation flow E hB hS)
