-- Prove2me | solution 1 for NoHair.TwoCentre.Cartesian.exterior_and_frontier
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T21:38:17.87281+00:00
-- url     : https://prove2.me/submissions/fbb9bfaf-c27c-44af-ad8e-67f7b2b23b20

import Definitions.Def_NoHair_TwoCentreSpacetime
import Definitions.Def_NoHair_spacetime

open NoHair NoHair.TwoCentre Set Topology
open scoped ContDiff Manifold

namespace NoHair.TwoCentre.Cartesian

private theorem coordinates_time (t : ℝ) (x : E3) : coordinates t x 0 = t := rfl
private theorem coordinates_spatial (t : ℝ) (x : E3) : spatial (coordinates t x) = x := by
  ext i
  simp [spatial, coordinates, Fin.cons_succ]

private theorem coordinates_recover (z : E4) : coordinates (z 0) (spatial z) = z := by
  ext i
  refine Fin.cases rfl (fun j => ?_) i
  simp [spatial, coordinates, Fin.cons_succ]

private theorem spatial_smooth : ContDiff ℝ ∞ spatial :=
  contDiff_euclidean.2 (fun i => contDiff_piLp_apply (p := 2) (i := i.succ))

private theorem coordinates_smooth : ContDiff ℝ ∞ (fun p : ℝ × E3 => coordinates p.1 p.2) := by
  apply contDiff_euclidean.2
  intro i
  refine Fin.cases (by exact contDiff_fst) (fun j => ?_) i
  simp only [coordinates, WithLp.ofLp_toLp, Fin.cons_succ]
  fun_prop

private noncomputable def splitHomeo : E4 ≃ₜ ℝ × E3 where
  toFun y := (y 0, spatial y)
  invFun p := coordinates p.1 p.2
  left_inv := coordinates_recover
  right_inv := fun ⟨t, x⟩ => Prod.ext (coordinates_time t x) (coordinates_spatial t x)
  continuous_toFun := ((contDiff_piLp_apply (p := 2) (i := (0 : Fin 4))
    (𝕜 := ℝ) (n := ∞)).continuous).prodMk spatial_smooth.continuous
  continuous_invFun := coordinates_smooth.continuous

private theorem unit_norm : ‖unitAxis‖ = 1 := by simp [unitAxis]

private theorem norm_squared (c : ℝ) (y : E4) :
    ‖spatial y - c • unitAxis‖ ^ 2 = squaredDistance c y := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  simp [spatial, unitAxis, squaredDistance, PiLp.sub_apply, PiLp.smul_apply]

private theorem exterior_iff (y : E4) :
    y ∈ exterior ↔ spatial y + unitAxis ≠ 0 ∧ spatial y + unitAxis ≠ (2 : ℝ) • unitAxis := by
  change 0 < squaredDistance (-1) y ∧ 0 < squaredDistance 1 y ↔ _
  rw [← norm_squared, ← norm_squared]
  simp only [neg_smul, one_smul, sub_neg_eq_add, sq_pos_iff, norm_ne_zero_iff,
    sub_ne_zero, two_smul]
  constructor
  · rintro ⟨hn, hh⟩
    exact ⟨hn, fun he => hh (add_right_cancel he)⟩
  · rintro ⟨hn, hh⟩
    exact ⟨hn, fun he => hh (congrArg (· + unitAxis) he)⟩

private theorem expanded_norm {a : E3} (ha : a ≠ 0) : ‖expandRadius a‖ = ‖a‖ + 1 := by
  have h := norm_pos_iff.mpr ha
  rw [expandRadius, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  field_simp

private theorem contracted_norm {a : E3} (ha : 1 < ‖a‖) : ‖contractRadius a‖ = ‖a‖ - 1 := by
  have hn : 0 < ‖a‖ := by linarith
  have hinv : ‖a‖⁻¹ < 1 := by simpa [one_div] using (div_lt_one hn).2 ha
  rw [contractRadius, norm_smul, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hinv)]
  field_simp

private theorem contract_expand {a : E3} (ha : a ≠ 0) : contractRadius (expandRadius a) = a := by
  have hn := norm_pos_iff.mpr ha
  rw [contractRadius, expanded_norm ha, expandRadius, smul_smul]
  rw [show (1 - (‖a‖ + 1)⁻¹) * (1 + ‖a‖⁻¹) = 1 by
    field_simp [hn.ne', show ‖a‖ + 1 ≠ 0 by linarith]; ring, one_smul]

private theorem expand_contract {a : E3} (ha : 1 < ‖a‖) : expandRadius (contractRadius a) = a := by
  have hn : 0 < ‖a‖ := by linarith
  rw [expandRadius, contracted_norm ha, contractRadius, smul_smul]
  rw [show (1 + (‖a‖ - 1)⁻¹) * (1 - ‖a‖⁻¹) = 1 by
    field_simp [hn.ne', (sub_pos.mpr ha).ne']; ring, one_smul]

private theorem pole_contract : contractRadius ((3 : ℝ) • unitAxis) = (2 : ℝ) • unitAxis := by
  simp only [contractRadius, norm_smul, Real.norm_eq_abs, unit_norm, mul_one, smul_smul]
  norm_num

private theorem pole_expand : expandRadius ((2 : ℝ) • unitAxis) = (3 : ℝ) • unitAxis := by
  simp only [expandRadius, norm_smul, Real.norm_eq_abs, unit_norm, mul_one, smul_smul]
  norm_num

private theorem shift_smooth {s : ℝ} (hs : s ≠ 0) : ContDiffAt ℝ ∞ timeShift s := by
  unfold timeShift
  fun_prop (disch := assumption)

private theorem toAdvanced_smooth {y : E4} (hy : y ∈ exterior) : ContDiffAt ℝ ∞ toAdvanced y := by
  let a := fun z => spatial z + unitAxis
  have ha : a y ≠ 0 := ((exterior_iff y).mp hy).1
  have hs : ContDiffAt ℝ ∞ a y := spatial_smooth.contDiffAt.add contDiffAt_const
  have hn : ContDiffAt ℝ ∞ (fun z => ‖a z‖) y := hs.norm ℝ ha
  change ContDiffAt ℝ ∞ ((fun p : ℝ × E3 => coordinates p.1 p.2) ∘
    (fun z => (z 0 + timeShift ‖a z‖, expandRadius (a z)))) y
  apply coordinates_smooth.contDiffAt.comp y
  exact ((contDiffAt_piLp_apply (p := 2) (i := (0 : Fin 4))).add
    ((shift_smooth (norm_ne_zero_iff.mpr ha)).comp y hn)).prodMk
    ((contDiffAt_const.add (hn.inv (norm_ne_zero_iff.mpr ha))).smul hs)

private theorem toIsotropic_smooth {z : E4} (hz : z ∈ outerRegion) : ContDiffAt ℝ ∞ toIsotropic z := by
  have h := hz.1
  have hz' : 0 < ‖spatial z‖ := by linarith
  have hs : ContDiffAt ℝ ∞ spatial z := spatial_smooth.contDiffAt
  have hn : ContDiffAt ℝ ∞ (fun y => ‖spatial y‖) z := hs.norm ℝ (norm_pos_iff.mp hz')
  change ContDiffAt ℝ ∞ ((fun p : ℝ × E3 => coordinates p.1 p.2) ∘
    (fun y => (y 0 - timeShift (‖spatial y‖ - 1), contractRadius (spatial y) - unitAxis))) z
  apply coordinates_smooth.contDiffAt.comp z
  exact ((contDiffAt_piLp_apply (p := 2) (i := (0 : Fin 4))).sub
    ((shift_smooth (sub_pos.mpr h).ne').comp z (hn.sub contDiffAt_const))).prodMk
    (((contDiffAt_const.sub (hn.inv hz'.ne')).smul hs).sub contDiffAt_const)

private theorem global_chart : IsDiffeoOnto toAdvanced exterior outerRegion := by
  refine ⟨toIsotropic, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨hn, hp⟩ := (exterior_iff y).mp hy
    change 1 < ‖spatial (toAdvanced y)‖ ∧ spatial (toAdvanced y) ≠ _
    simp only [toAdvanced, coordinates_spatial, expanded_norm hn]
    refine ⟨by linarith [norm_pos_iff.mpr hn], ?_⟩
    intro hh
    apply hp
    simpa only [contract_expand hn, pole_contract] using congrArg contractRadius hh
  · intro z hz
    apply (exterior_iff _).mpr
    simp only [toIsotropic, coordinates_spatial, sub_add_cancel]
    refine ⟨norm_pos_iff.mp (by rw [contracted_norm hz.1]; exact sub_pos.mpr hz.1), ?_⟩
    intro hh
    apply hz.2
    simpa only [expand_contract hz.1, pole_expand] using congrArg expandRadius hh
  · intro y hy
    have h := ((exterior_iff y).mp hy).1
    simp only [toIsotropic, toAdvanced, coordinates_time, coordinates_spatial, expanded_norm h,
      add_sub_cancel_right, contract_expand h, coordinates_recover]
  · intro z hz
    simp only [toAdvanced, toIsotropic, coordinates_time, coordinates_spatial, sub_add_cancel,
      contracted_norm hz.1, expand_contract hz.1, coordinates_recover]
  · exact fun y hy => (toAdvanced_smooth hy).contMDiffAt.contMDiffWithinAt
  · exact fun z hz => (toIsotropic_smooth hz).contMDiffAt.contMDiffWithinAt

private theorem spacetime_open : IsOpen spacetime :=
  (isOpen_lt continuous_const spatial_smooth.continuous.norm).inter
    (isOpen_ne_fun spatial_smooth.continuous continuous_const)

private theorem shell_in_spacetime {z : E4} (hz : z ∈ horizon) : z ∈ spacetime := by
  change ‖spatial z‖ = 1 at hz
  refine ⟨by linarith, ?_⟩
  intro he
  rw [he, norm_smul, unit_norm, mul_one] at hz
  norm_num at hz

private theorem frontier_shell :
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

private theorem connected_shell : IsConnected {z : spacetime | (z : E4) ∈ horizon} := by
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

open NoHair.TwoCentre.Cartesian

/-- One open Cartesian coordinate manifold contains a complete copy of the
two-centre exterior and the collar at its left pole. Its exterior has exactly
one connected frontier, the unit sphere of each advanced time slice. -/
theorem solution :
    IsOpen spacetime ∧ IsDiffeoOnto toAdvanced exterior outerRegion ∧
    frontier {z : spacetime | (z : E4) ∈ outerRegion} = {z : spacetime | (z : E4) ∈ horizon} ∧
    IsConnected {z : spacetime | (z : E4) ∈ horizon} := by
  exact ⟨spacetime_open, global_chart, frontier_shell, connected_shell⟩
