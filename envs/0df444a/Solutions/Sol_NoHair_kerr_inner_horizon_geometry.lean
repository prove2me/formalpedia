-- Prove2me | solution 1 for NoHair.kerr_inner_horizon_geometry
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T23:07:55.979854+00:00
-- url     : https://prove2.me/submissions/20d56dab-a3c0-4395-a354-af42c03550c4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_NoHair_KerrNewmanEinstein_Base
import Theorems.Thm_NoHair_ksRadius_superlevel_frontier
import Theorems.Thm_NoHair_kerr_inner_helical_symmetry
import Theorems.Thm_NoHair_kerr_inner_horizon_normal_identity

open NoHair Set
open scoped ContDiff Manifold BigOperators Topology

private theorem entry (A : Matrix (Fin 4) (Fin 4) ℝ) (i j : Fin 4) :
    matrixBilin A (coordBasis i) (coordBasis j) = A i j := by
  change Matrix.toLinearMap₂' ℝ A (WithLp.ofLp (coordBasis i)) (WithLp.ofLp (coordBasis j)) = _
  simp only [coordBasis, EuclideanSpace.single, PiLp.ofLp_single]
  rw [Matrix.toLinearMap₂'_apply]
  simp_rw [← Finset.smul_sum]
  simp [Pi.single_apply, ite_smul, Finset.sum_ite_eq, Finset.sum_ite_eq']

private theorem analytic_restrict (U : TopologicalSpace.Opens E4) (A : E4 → Matrix (Fin 4) (Fin 4) ℝ)
    (h : ∀ y ∈ U, ∀ i j, ContDiffAt ℝ ω (fun z => A z i j) y) :
    IsAnalyticBilinField (M := U) (fun x => matrixBilin (A x.val)) := by
  intro c hc i j y hy
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
  have coeff (z : E4) (hz : z ∈ c.target) :
      pullbackCoeffs (M := U) (fun x => matrixBilin (A x.val)) c.symm z i j = A z i j := by
    have hd := derivAt (c.symm z)
    rw [hval z hz] at hd
    unfold pullbackCoeffs
    rw [hd]
    change matrixBilin (A (c.symm z).val) (coordBasis i) (coordBasis j) = A z i j
    rw [hval z hz, entry]
  have hs : ContDiffOn ℝ ω (fun z => A z i j) c.target := by
    intro z hz
    have hzU : z ∈ U := (hval z hz) ▸ (c.symm z).property
    exact (h z hzU i j).contDiffWithinAt
  exact (hs.congr coeff) y hy

private theorem radius_smooth (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    ContDiffAt ℝ ω (ksRadius a) z := by
  have hD := (ks_D_pos a z hz).ne'
  have hQ := (ks_Q_pos a z hz).ne'
  rw [ksRadius_eq']
  fun_prop (disch := assumption)

private theorem null_smooth (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) (i : Fin 4) :
    ContDiffAt ℝ ω (fun w => ksNull a w i) z := by
  have hr := radius_smooth a z hz
  have hne : ksRadius a z ^ 2 + a ^ 2 ≠ 0 := by positivity
  have hne' := hz.ne'
  fin_cases i
  · simp only [Fin.zero_eta, ksNull_zero]; fun_prop
  · simp only [Fin.mk_one, ksNull_one]; fun_prop (disch := assumption)
  · change ContDiffAt ℝ ω (fun w => ksNull a w 2) z
    simp only [ksNull_two]; fun_prop (disch := assumption)
  · change ContDiffAt ℝ ω (fun w => ksNull a w 3) z
    simp only [ksNull_three]; fun_prop (disch := assumption)

theorem solution :
    let A := {x : kerrNewmanSpacetime 2 | 1 < ksRadius 2 x.val}
    let g := kerrNewmanMetricField (5/2) 2 0
    let F := kerrNewmanFieldField 2 0
    IsAnalyticBilinField g ∧ Aᶜ.Nonempty ∧ IsConnected (frontier A) ∧
      IsNondegenerateHorizon g F (frontier A) A := by
  let A := {x : kerrNewmanSpacetime 2 | 1 < ksRadius 2 x.val}
  let X : VecField (kerrNewmanSpacetime 2) :=
    fun x => WithLp.toLp 2 ![1,-(2/5)*x.val 2,(2/5)*x.val 1,0]
  obtain ⟨hfront,hlevel⟩ := ksRadius_superlevel_frontier 2 1 (by norm_num)
  have hfront' : frontier A={x : kerrNewmanSpacetime 2 | ksRadius 2 x.val=1} := hfront
  obtain ⟨x,hx⟩ := hlevel.nonempty
  have hx' : ksRadius 2 x.val=1 := hx
  have hxH : x ∈ frontier A := by rw [hfront']; exact hx
  obtain ⟨χ,hχ,hX⟩ := kerr_inner_helical_symmetry
  refine ⟨?_,⟨x,not_lt_of_ge hx'.le⟩,(by change IsConnected (frontier A); rw [hfront']; exact hlevel),χ,-3/10,hχ,by norm_num,?_,?_⟩
  · apply analytic_restrict (kerrNewmanSpacetime 2) (kerrNewmanMetric (5/2) 2 0)
    intro y hy i j
    have hpos : 0 < ksRadius 2 y := hy
    have hr := radius_smooth 2 y hpos
    have hi := null_smooth 2 y hpos i
    have hj := null_smooth 2 y hpos j
    have hd := (ks_den_pos 2 y hpos).ne'
    unfold kerrNewmanMetric ksProfile
    fun_prop (disch := assumption)
  · refine ⟨x,⟨hxH,frontier_subset_closure hxH⟩,?_⟩
    rw [hX]
    intro hzero
    have he := congrArg (fun v : E4 => v 0) hzero
    change (1:ℝ)=0 at he
    norm_num at he
  · intro y hy
    have hmem := hy.1
    rw [hfront'] at hmem
    rw [hX]
    have h := kerr_inner_horizon_normal_identity y hmem
    simpa only [show (-2:ℝ)*(-3/10)=3/5 by norm_num] using h
