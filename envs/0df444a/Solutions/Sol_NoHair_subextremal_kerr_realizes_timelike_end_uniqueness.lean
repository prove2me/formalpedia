-- Prove2me | solution 1 for NoHair.subextremal_kerr_realizes_timelike_end_uniqueness
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T10:11:35.51626+00:00
-- url     : https://prove2.me/submissions/712a23d2-957e-4899-93d9-7e59aae3afb5

import Theorems.Thm_NoHair_kerrNewman_asymptoticComponentBounds
import Definitions.Def_NoHair_KerrNewmanEinstein_Base
import Theorems.Thm_NoHair_kerrNewman_stationaryFlatEnd
import Theorems.Thm_NoHair_kerrNewman_isStationaryBlackHole
import Theorems.Thm_NoHair_kerrNewman_outerHorizon_futureTrapped
import Theorems.Thm_NoHair_kerrNewman_exterior_globallyHyperbolic
import Theorems.Thm_NoHair_kerrNewman_chronology_at_infinity
import Theorems.Thm_NoHair_kerr_stationary_uniform_timelike_radius
import Theorems.Thm_NoHair_timelike_reference_end_chronology_at_infinity
import Theorems.Thm_NoHair_ksRadius_superlevel_frontier
import Theorems.Thm_NoHair_kerr_horizon_generator_at_positive_root

open NoHair Set
open scoped ContDiff Manifold BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
private abbrev I4 := 𝓘(ℝ,E4)

private theorem inclusion_deriv (U : TopologicalSpace.Opens E4) (x : U) :
    (mfderiv I4 I4 (Subtype.val : U → E4) x : E4 →L[ℝ] E4) = ContinuousLinearMap.id ℝ E4 :=
  mfderiv_extChartAt_self (I := I4) (x := x)

private theorem inclusion_diff (U : TopologicalSpace.Opens E4) (x : U) :
    MDifferentiableAt I4 I4 (Subtype.val : U → E4) x :=
  (contMDiff_subtype_val (I := I4) (U := U) (n := ∞)).mdifferentiableAt (by simp)

private theorem basis_entry (A : Matrix (Fin 4) (Fin 4) ℝ) (i j : Fin 4) :
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
    rw [hval z hz, basis_entry]
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

private theorem chart_end (m a e cutoff : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e) :
    ∃ (φ : ℝ → kerrNewmanSpacetime a → kerrNewmanSpacetime a)
      (E : AsymptoticallyFlatEnd (kerrNewmanMetricField m a e) (kerrNewmanFieldField a e) φ),
      (∀ s x, (φ s x).val = x.val + s • coordBasis 0) ∧
      IsSymmetryFlow (kerrNewmanMetricField m a e) (kerrNewmanFieldField a e) φ ∧
      cutoff < E.R ∧ ∀ u, E.R ≤ u → E.ψ '' exteriorRegion u =
        (Subtype.val : kerrNewmanSpacetime a → E4) ⁻¹' exteriorRegion u := by
  classical
  let U := kerrNewmanSpacetime a
  obtain ⟨φ, _, hφ, hstation, _, _⟩ := kerrNewman_stationaryFlatEnd m a e hp
  obtain ⟨R, C, hR, hbounds⟩ := kerrNewman_asymptoticComponentBounds m a e cutoff
  have hR0 : 0 < R := (le_max_left _ _).trans_lt hR
  let S := exteriorRegion R
  have hS : IsOpen S := by
    apply isOpen_lt continuous_const
    unfold spatialRadius
    fun_prop
  let y₀ : E4 := WithLp.toLp 2 ![0, R+1, 0, 0]
  have hy₀ : y₀ ∈ S := by
    change R < Real.sqrt ((R+1)^2 + 0^2 + 0^2)
    simp [Real.sqrt_sq_eq_abs, abs_of_pos (show 0 < R+1 by linarith)]
  let x₀ : U := ⟨y₀, (hbounds y₀ hy₀).1⟩
  let ψ (y : E4) : U := if h : y ∈ U then ⟨y,h⟩ else x₀
  have hv' (y : E4) (hy : y ∈ U) : (ψ y).val = y := by simp [ψ, hy]
  have hv (y : E4) (hy : y ∈ S) : (ψ y).val = y := hv' y (hbounds y hy).1
  have himg : ψ '' S = (Subtype.val : U → E4) ⁻¹' S := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      change (ψ y).val ∈ S
      rwa [hv y hy]
    · intro hx
      exact ⟨x.val, hx, Subtype.ext (hv x.val hx)⟩
  have hgerm : EqOn ((Subtype.val : U → E4) ∘ ψ) id S := hv
  have hsm : ContMDiffOn I4 I4 ∞ ψ S := by
    intro z hz
    apply (ContMDiffWithinAt.subtypeVal_comp_iff U ψ S z).mp
    exact ((contMDiff_id (I := I4)).contMDiffOn.congr (fun w hw => hgerm hw)) z hz
  have hder (y : E4) (hy : y ∈ S) :
      (mfderiv I4 I4 ψ y : E4 →L[ℝ] E4) = ContinuousLinearMap.id ℝ E4 := by
    have hψ := ((hsm y hy).contMDiffAt (hS.mem_nhds hy)).mdifferentiableAt (by simp)
    have hc := mfderiv_comp y (inclusion_diff U (ψ y)) hψ
    rw [inclusion_deriv] at hc
    change mfderiv I4 I4 ((Subtype.val : U → E4) ∘ ψ) y = (mfderiv I4 I4 ψ y : E4 →L[ℝ] E4) at hc
    rw [← hc, mfderiv_eq_fderiv, (hgerm.eventuallyEq_of_mem (hS.mem_nhds hy)).fderiv_eq, fderiv_id]
  have hcoeff (A : E4 → Matrix (Fin 4) (Fin 4) ℝ) (y : E4) (hy : y ∈ S) (i j : Fin 4) :
      pullbackCoeffs (M := U) (fun x => matrixBilin (A x.val)) ψ y i j = A y i j := by
    unfold pullbackCoeffs
    rw [hder y hy]
    change matrixBilin (A (ψ y).val) (coordBasis i) (coordBasis j) = A y i j
    rw [hv y hy, basis_entry]
  let E : AsymptoticallyFlatEnd (kerrNewmanMetricField m a e) (kerrNewmanFieldField a e) φ := {
    R := R, ψ := ψ, C := C, R_pos := hR0
    diffeo := by
      refine ⟨Subtype.val, mapsTo_image _ _, ?_, hv, ?_, hsm, contMDiff_subtype_val.contMDiffOn⟩
      · rw [himg]; exact fun _ hx => hx
      · rw [himg]; exact fun x hx => Subtype.ext (hv x.val hx)
    isOpen_image := by rw [himg]; exact hS.preimage continuous_subtype_val
    equivariant := by
      intro s y hy
      have hshift : y + s • coordBasis 0 ∈ S := by
        change R < spatialRadius (y + s • coordBasis 0)
        have heq : spatialRadius (y + s • coordBasis 0) = spatialRadius y := by
          simp only [spatialRadius, NoHair.KNE.time_shift y s 1 (by decide),
            NoHair.KNE.time_shift y s 2 (by decide), NoHair.KNE.time_shift y s 3 (by decide)]
        rwa [heq]
      exact Subtype.ext (by rw [hv _ hshift, hφ, hv y hy])
    metric_decay := by
      intro y hy i j
      have hentry : pullbackCoeffs (kerrNewmanMetricField m a e) ψ y i j = _ := hcoeff (kerrNewmanMetric m a e) y hy i j
      rw [hentry]
      exact (hbounds y hy).2.1 i j
    metric_deriv_decay := by
      intro y hy i j k
      have he : EqOn (fun w => pullbackCoeffs (kerrNewmanMetricField m a e) ψ w i j)
          (fun w => kerrNewmanMetric m a e w i j) S := fun w hw => hcoeff _ w hw i j
      unfold coordPartial
      rw [(he.eventuallyEq_of_mem (hS.mem_nhds hy)).fderiv_eq]
      exact (hbounds y hy).2.2.1 i j k
    field_decay := by
      intro y hy i j
      have hentry : pullbackCoeffs (kerrNewmanFieldField a e) ψ y i j = _ := hcoeff (kerrNewmanField a e) y hy i j
      rw [hentry]
      exact (hbounds y hy).2.2.2 i j }
  refine ⟨φ,E,hφ,hstation,(le_max_right _ _).trans_lt hR,?_⟩
  intro u hu
  have sub : exteriorRegion u ⊆ S := fun y hy => lt_of_le_of_lt hu hy
  change ψ '' exteriorRegion u = (Subtype.val : U → E4) ⁻¹' exteriorRegion u
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    change (ψ y).val ∈ exteriorRegion u
    rwa [hv _ (sub hy)]
  · intro hx
    exact ⟨x.val,hx,Subtype.ext (hv x.val (sub hx))⟩

theorem solution (m a : ℝ) (hm : 0 < m) (hsub : a^2 < m^2) :
    let g := kerrNewmanMetricField m a 0
    let F := kerrNewmanFieldField a 0
    let T := kerrNewmanTimeDirection m a 0
    let R := kerrNewmanOuterRadius m a 0
    ∃ (φ : ℝ → kerrNewmanSpacetime a → kerrNewmanSpacetime a) (E : AsymptoticallyFlatEnd g F φ),
      (∀ x ∈ E.region, g x (flowGenerator φ x) (flowGenerator φ x) < 0) ∧
      IsStationaryBlackHole g F T φ E ∧ (∀ x, F x = 0) ∧ IsAnalyticBilinField g ∧
      (domainOfOuterCommunications g T E.region = (Subtype.val : kerrNewmanSpacetime a → E4) ⁻¹' kerrNewmanDOC m a 0) ∧
      (futureEventHorizon g T E.region = {x : kerrNewmanSpacetime a | ksRadius a x.val = R}) ∧
      IsNondegenerateHorizon g F (futureEventHorizon g T E.region) (domainOfOuterCommunications g T E.region) ∧
      0 < (R-m)/(R^2+a^2) ∧ IsKerrNewmanDOC g F (domainOfOuterCommunications g T E.region) m a 0 := by
  let g := kerrNewmanMetricField m a 0
  let F := kerrNewmanFieldField a 0
  let T := kerrNewmanTimeDirection m a 0
  let R := kerrNewmanOuterRadius m a 0
  let Z := kerrNewmanSpacetime a
  let S : Set Z := (Subtype.val : Z → E4) ⁻¹' kerrNewmanDOC m a 0
  let A := fun u : ℝ => {x : Z | u < ksRadius a x.val}
  let C := fun u : ℝ => (Subtype.val : Z → E4) ⁻¹' exteriorRegion u
  have hpar : IsKerrNewmanBlackHoleParams m a 0 := ⟨hm,by simpa using hsub.le⟩
  have hRval : R = m+Real.sqrt (m^2-a^2) := by simp [R,kerrNewmanOuterRadius]
  have hdis : 0 < m^2-a^2 := sub_pos.mpr hsub
  have hrm : m < R := by rw [hRval]; linarith [Real.sqrt_pos.2 hdis]
  have hR := hm.trans hrm
  have hroot : R^2-2*m*R+a^2=0 := by rw [hRval]; nlinarith only [Real.sq_sqrt hdis.le]
  obtain ⟨φ,E,hφ,hsym,hRE,htail⟩ := chart_end m a 0 (2*m+|a|) hpar
  let B := fun u : ℝ => E.ψ '' exteriorRegion u
  change ∀ u, E.R ≤ u → B u = C u at htail
  obtain ⟨geo,hinf⟩ := kerrNewman_chronology_at_infinity m a 0 E.R hpar
  change ∀ u, A u ⊆ C u ∧ C (u+|a|) ⊆ A u at geo
  have Bmono : Antitone B := fun r s hrs => image_mono (fun y hy => lt_of_le_of_lt hrs hy)
  have Cmono : Antitone C := fun r s hrs x hx => lt_of_le_of_lt hrs hx
  have ab (r : ℝ) : ∃ u, A u ⊆ B r := by
    let u := max E.R r
    exact ⟨u,(geo u).1.trans ((htail u (le_max_left _ _)).symm ▸ Bmono (le_max_right E.R r))⟩
  have ba (r : ℝ) : ∃ u, B u ⊆ A r := by
    let u := max E.R (r+|a|)
    refine ⟨u,?_⟩
    rw [htail _ (le_max_left _ _)]
    exact (Cmono (le_max_right E.R (r+|a|))).trans (geo r).2
  obtain ⟨hpinf,hdinf,hhinf,hiso⟩ := hinf B Bmono ab ba
  obtain ⟨T',φ',E',hphys,_⟩ := kerrNewman_isStationaryBlackHole m a 0 hpar
  obtain ⟨ht,_⟩ := kerrNewman_outerHorizon_futureTrapped m a 0 hpar
  have htime : ∀ x ∈ E.region, g x (flowGenerator φ x) (flowGenerator φ x) < 0 := by
    intro x hx
    have hc : x ∈ C E.R := htail E.R le_rfl ▸ hx
    have ha := (geo (2*m)).2 (Cmono hRE.le hc)
    have him := (kerr_stationary_uniform_timelike_radius m a (2*m) 0 hm ⟨le_rfl,by norm_num⟩ φ hφ hsym).2 (by ring_nf; rfl)
    simpa [g] using him x ha
  obtain ⟨hps,_,hds,hhs⟩ := timelike_reference_end_chronology_at_infinity E hphys.lorentzian hphys.smooth_metric T ht hsym htime
  let D := domainOfOuterCommunications g T E.region
  let H := futureEventHorizon g T E.region
  have hp : chronoPastSet g T E.region = S := hps.symm.trans hpinf
  have hd : D = S := hds.symm.trans hdinf
  have hh : H = {x : Z | ksRadius a x.val = R} := hhs.symm.trans hhinf
  obtain ⟨hfront,hlevel⟩ := ksRadius_superlevel_frontier a R hR
  change frontier S = {x : Z | ksRadius a x.val=R} at hfront
  obtain ⟨p,hpR⟩ := hlevel.nonempty
  have hpR' : ksRadius a p.val = R := hpR
  have pH : p ∈ H := hh.symm ▸ hpR
  have pcl : p ∈ closure D := by rw [hd]; exact frontier_subset_closure (hfront.symm ▸ hpR)
  have bh : IsStationaryBlackHole g F T φ E :=
    { lorentzian := hphys.lorentzian, smooth_metric := hphys.smooth_metric, smooth_field := hphys.smooth_field,
      twoForm := hphys.twoForm, timeOrientation := ht, electrovac := hphys.electrovac, stationary := hsym,
      globallyHyperbolic := by
        change IsGloballyHyperbolicOn g T D
        rw [hd]
        exact kerrNewman_exterior_globallyHyperbolic m a 0 hpar T ht,
      blackHole_nonempty := ⟨p,by change p ∉ chronoPastSet g T E.region; rw [hp]; exact not_lt_of_ge hpR'.le⟩,
      horizon_connected := by change IsConnected H; rw [hh]; exact hlevel }
  have hvac (x : Z) : F x=0 := by
    have he : kerrNewmanField a 0 x.val=0 := by
      ext i j; simp [kerrNewmanField,coordPartial,kerrNewmanPotential]
    change matrixBilin (kerrNewmanField a 0 x.val)=0
    rw [he]; ext v w; simp [matrixBilin,Matrix.toLinearMap₂'_apply]
  have han : IsAnalyticBilinField g := by
    apply analytic_restrict (kerrNewmanSpacetime a) (kerrNewmanMetric m a 0)
    intro y hy i j
    have hpos : 0 < ksRadius a y := hy
    have hr := radius_smooth a y hpos
    have hi := null_smooth a y hpos i
    have hj := null_smooth a y hpos j
    have den := (ks_den_pos a y hpos).ne'
    unfold kerrNewmanMetric ksProfile
    fun_prop (disch := assumption)
  have hk : 0 < (R-m)/(R^2+a^2) := div_pos (sub_pos.mpr hrm) (by positivity)
  obtain ⟨χ,hχ,hX,hid⟩ := kerr_horizon_generator_at_positive_root m a R hR hroot
  have hnd : IsNondegenerateHorizon g F H D := by
    refine ⟨χ,(R-m)/(R^2+a^2),hχ,hk.ne',⟨p,⟨pH,pcl⟩,?_⟩,?_⟩
    · intro hz
      have he := congrArg (fun v : E4 => v 0) ((hX p).symm.trans hz)
      change (1:ℝ)=0 at he
      norm_num at he
    · intro x hx
      have hxH : x ∈ H := hx.1
      rw [hh] at hxH
      exact hid x hxH
  exact ⟨φ,E,htime,bh,hvac,han,hd,hh,hnd,hk,hds ▸ hiso⟩
