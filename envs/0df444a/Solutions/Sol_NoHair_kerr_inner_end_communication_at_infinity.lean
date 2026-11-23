-- Prove2me | solution 1 for NoHair.kerr_inner_end_communication_at_infinity
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T08:43:09.182802+00:00
-- url     : https://prove2.me/submissions/447fc6c0-3dc9-440e-ba0f-a5f03f52a301

import Theorems.Thm_NoHair_kerrNewman_chronology_at_infinity
import Theorems.Thm_NoHair_kerrNewman_regularTensors
import Theorems.Thm_NoHair_isElectrovac_of_coordinate_equations
import Theorems.Thm_NoHair_kerrNewman_einsteinMaxwell
import Theorems.Thm_NoHair_kerrNewman_stationaryFlatEnd
import Theorems.Thm_NoHair_kerrNewman_outerHorizon_futureTrapped
import Theorems.Thm_NoHair_kerr_oblate_chart_component_decay
import Theorems.Thm_NoHair_kerr_inner_horizon_chronology
import Theorems.Thm_NoHair_kerr_inner_horizon_global_hyperbolicity
import Theorems.Thm_NoHair_kerr_inner_horizon_geometry
import Theorems.Thm_NoHair_kerr_inner_horizon_shell_not_exterior
import Theorems.Thm_NoHair_ksRadius_superlevel_frontier
import Definitions.Def_NoHair_KerrNewmanEinstein_Atoms

open NoHair NoHair.KNE Set Filter
open scoped ContDiff Manifold BigOperators Topology

noncomputable section

private abbrev I4 := 𝓘(ℝ,E4)
private def four (t x y z : ℝ) : E4 := WithLp.toLp 2 ![t,x,y,z]
private def oblate (a r t X Y Z : ℝ) := four t (r*X-a*Y) (a*X+r*Y) (r*Z)
private def sigma (a Z r : ℝ) := r^2+a^2*Z^2
private def bigP (a r : ℝ) := r^2+a^2
private def massTerm (m e r : ℝ) := 2*m*r-e^2

private theorem oblate_data (a r t X Y Z : ℝ) (hr : 0 < r) (hk : X^2+Y^2+Z^2=1) :
    let y := oblate a r t X Y Z
    ksRadius a y = r ∧ ksNull a y = ![1,X,Y,Z] ∧ r  ≤  spatialRadius y := by
  let ρ2 := (r*X-a*Y)^2+(a*X+r*Y)^2+(r*Z)^2
  have hρ : ρ2 = r^2+a^2*(1-Z^2) := by
    dsimp [ρ2]; linear_combination (r^2+a^2)*hk
  have hs : 0  ≤  r^2+a^2*Z^2 := by positivity
  have hc : ρ2-a^2 = r^2-a^2*Z^2 := by rw [hρ]; ring
  have hD : (ρ2-a^2)^2+4*a^2*(r*Z)^2 = (r^2+a^2*Z^2)^2 := by rw [hc]; ring
  have hrad : ksRadius a (oblate a r t X Y Z) = r := by
    change Real.sqrt ((ρ2-a^2+Real.sqrt ((ρ2-a^2)^2+4*a^2*(r*Z)^2))/2)=r
    rw [hD, Real.sqrt_sq hs, hc]
    convert Real.sqrt_sq hr.le using 2 <;> ring
  refine ⟨hrad, ?_, ?_⟩
  · unfold ksNull
    rw [hrad]
    have hden : r^2+a^2  ≠  0 := by positivity
    funext i
    fin_cases i <;> simp [four,oblate, hden, hr.ne'] <;> field_simp [hden,hr.ne'] <;> ring
  · change r  ≤  Real.sqrt ρ2
    have hxy : 0  ≤  1-Z^2 := by nlinarith only [hk,sq_nonneg X,sq_nonneg Y]
    apply Real.le_sqrt_of_sq_le
    rw [hρ]; linarith [mul_nonneg (sq_nonneg a) hxy]

private def raw (y : E4) : E4 :=
  four (y 0) (y 1-2*(y 2/spatialRadius y)) (y 2+2*(y 1/spatialRadius y)) (y 3)

private theorem radius_sq (y : E4) : spatialRadius y ^ 2 = y 1 ^ 2+y 2 ^ 2+y 3 ^ 2 :=
  Real.sq_sqrt (by positivity)

private theorem raw_data (y : E4) (hr : 0 < spatialRadius y) :
    ksRadius 2 (raw y)=spatialRadius y ∧ ksNull 2 (raw y)=
      ![1,y 1/spatialRadius y,y 2/spatialRadius y,y 3/spatialRadius y] := by
  let r := spatialRadius y
  have hu : (y 1/r)^2+(y 2/r)^2+(y 3/r)^2=1 := by
    field_simp [show r≠0 from hr.ne']; linear_combination -(radius_sq y)
  have he : raw y=oblate 2 r (y 0) (y 1/r) (y 2/r) (y 3/r) := by
    ext i; fin_cases i <;> simp [raw,oblate,four,r,hr.ne'] <;> field_simp [hr.ne'] <;> ring
  obtain ⟨h1,h2,_⟩ := oblate_data 2 r (y 0) _ _ _ hr hu
  rw [he]; exact ⟨h1,h2⟩

private theorem spatial_smooth (y : E4) (hy : 0 < spatialRadius y) : ContDiffAt ℝ ∞ spatialRadius y := by
  have hn : y 1^2+y 2^2+y 3^2 ≠ 0 := by rw [← radius_sq]; positivity
  unfold spatialRadius
  fun_prop (disch := assumption)

private theorem raw_smooth (y : E4) (hr : 0 < spatialRadius y) : ContDiffAt ℝ ∞ raw y := by
  have hd := spatial_smooth y hr
  have hn := hr.ne'
  apply (contDiffAt_piLp 2).mpr
  intro i
  fin_cases i
  · change ContDiffAt ℝ ∞ (fun w : E4 => w 0) y; fun_prop
  · change ContDiffAt ℝ ∞ (fun w : E4 => w 1-2*(w 2/spatialRadius w)) y; fun_prop (disch := assumption)
  · change ContDiffAt ℝ ∞ (fun w : E4 => w 2+2*(w 1/spatialRadius w)) y; fun_prop (disch := assumption)
  · change ContDiffAt ℝ ∞ (fun w : E4 => w 3) y; fun_prop
private theorem radius_smooth (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    ContDiffAt ℝ ∞ (ksRadius a) z := by
  have hD := (ks_D_pos a z hz).ne'
  have hQ := (ks_Q_pos a z hz).ne'
  rw [ksRadius_eq']
  fun_prop (disch := assumption)

private theorem null_smooth (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) (i : Fin 4) :
    ContDiffAt ℝ ∞ (fun w => ksNull a w i) z := by
  have hr := radius_smooth a z hz
  have hne : ksRadius a z ^ 2 + a ^ 2 ≠ 0 := by positivity
  have hne' := hz.ne'
  fin_cases i
  · simp only [Fin.zero_eta, ksNull_zero]; fun_prop
  · simp only [Fin.mk_one, ksNull_one]; fun_prop (disch := assumption)
  · change ContDiffAt ℝ ∞ (fun w => ksNull a w 2) z
    simp only [ksNull_two]; fun_prop (disch := assumption)
  · change ContDiffAt ℝ ∞ (fun w => ksNull a w 3) z
    simp only [ksNull_three]; fun_prop (disch := assumption)

private def inverseRaw (z : E4) : E4 :=
  four (z 0) (ksRadius 2 z*ksNull 2 z 1) (ksRadius 2 z*ksNull 2 z 2) (ksRadius 2 z*ksNull 2 z 3)

private theorem inverse_data (z : E4) (hr : 0 < ksRadius 2 z) :
    spatialRadius (inverseRaw z)=ksRadius 2 z ∧ raw (inverseRaw z)=z := by
  let r := ksRadius 2 z
  let k := ksNull 2 z
  have hunit := ks_rel 2 z hr
  have hs : spatialRadius (inverseRaw z)=r := by
    change Real.sqrt ((r*k 1)^2+(r*k 2)^2+(r*k 3)^2)=r
    have h : (r*k 1)^2+(r*k 2)^2+(r*k 3)^2=r^2 := by
      change k 1^2+k 2^2+k 3^2=1 at hunit
      linear_combination r^2*hunit
    rw [h,Real.sqrt_sq hr.le]
  refine ⟨hs,?_⟩
  unfold raw
  rw [hs]
  have h1 := ks_x1 2 z hr
  have h2 := ks_x2 2 z hr
  have h3 := ks_x3 2 z hr
  have hn : r ≠ 0 := hr.ne'
  ext i; fin_cases i
  · rfl
  · change r*k 1-2*(r*k 2/r)=z 1
    rw [show r*k 2/r = k 2 by field_simp]
    exact h1.symm
  · change r*k 2+2*(r*k 1/r)=z 2
    rw [show r*k 1/r=k 1 by field_simp,add_comm]
    exact h2.symm
  · exact h3.symm

private theorem inverse_after (y : E4) (hr : 0 < spatialRadius y) : inverseRaw (raw y)=y := by
  obtain ⟨hr',hk⟩ := raw_data y hr
  unfold inverseRaw
  rw [hr',hk]
  ext i; fin_cases i <;> simp [four,raw,hr.ne'] <;> field_simp [hr.ne']

private theorem inverse_smooth (z : E4) (hz : 0 < ksRadius 2 z) : ContDiffAt ℝ ∞ inverseRaw z := by
  have hr := radius_smooth 2 z hz
  have h1 := null_smooth 2 z hz 1
  have h2 := null_smooth 2 z hz 2
  have h3 := null_smooth 2 z hz 3
  apply (contDiffAt_piLp 2).mpr
  intro i
  fin_cases i
  · change ContDiffAt ℝ ∞ (fun w : E4 => w 0) z; fun_prop
  · exact hr.mul h1
  · exact hr.mul h2
  · exact hr.mul h3

private theorem wide_end (φ : ℝ → kerrNewmanSpacetime 2 → kerrNewmanSpacetime 2)
    (hφ : ∀ s x, (φ s x).val = x.val+s • coordBasis 0) :
    ∃ E : AsymptoticallyFlatEnd (kerrNewmanMetricField (5/2) 2 0) (kerrNewmanFieldField 2 0) φ,
      E.R = 1 ∧ E.region = {x : kerrNewmanSpacetime 2 | 1 < ksRadius 2 x.val} ∧
      ∀ y ∈ exteriorRegion 1, ksRadius 2 (E.ψ y).val = spatialRadius y := by
  classical
  let U := kerrNewmanSpacetime 2
  let A := {x : U | 1<ksRadius 2 x.val}
  let S := exteriorRegion 1
  have hS : IsOpen S := isOpen_lt continuous_const (by unfold spatialRadius; fun_prop)
  have hA : IsOpen A := isOpen_lt continuous_const ((continuous_ksRadius 2).comp continuous_subtype_val)
  let base := four 0 0 0 2
  have hbase : 0<spatialRadius base := by change 0 < Real.sqrt ((0:ℝ)^2+0^2+2^2); norm_num
  let x₀ : U := ⟨raw base,by change 0<ksRadius 2 (raw base); rwa [(raw_data base hbase).1]⟩
  let ψ (y : E4) : U := if h : raw y ∈ U then ⟨raw y,h⟩ else x₀
  have hv (y : E4) (hy : y ∈ S) : (ψ y).val=raw y := by
    have hr : 0<spatialRadius y := zero_lt_one.trans hy
    have hU : raw y∈U := by change 0<ksRadius 2 (raw y); rwa [(raw_data y hr).1]
    simp [ψ,hU]
  let χ (x : U) := inverseRaw x.val
  have hψ : MapsTo ψ S A := by
    intro y hy
    change 1<ksRadius 2 (ψ y).val
    rw [hv y hy,(raw_data y (zero_lt_one.trans hy)).1]; exact hy
  have hχ : MapsTo χ A S := by
    intro x hx
    change 1<spatialRadius (inverseRaw x.val)
    rwa [(inverse_data x.val x.property).1]
  have hl : LeftInvOn χ ψ S := by
    intro y hy
    change inverseRaw (ψ y).val=y
    rw [hv y hy]
    exact inverse_after y (zero_lt_one.trans hy)
  have hr : RightInvOn χ ψ A := by
    intro x hx
    apply Subtype.ext
    rw [hv _ (hχ hx)]
    exact (inverse_data x.val x.property).2
  have hImg : ψ '' S=A := Subset.antisymm hψ.image_subset (fun x hx => ⟨χ x,hχ hx,hr hx⟩)
  have hsψ : ContMDiffOn I4 I4 ∞ ψ S := by
    intro y hy
    apply (ContMDiffWithinAt.subtypeVal_comp_iff U ψ S y).mp
    exact (raw_smooth y (zero_lt_one.trans hy)).contMDiffAt.contMDiffWithinAt.congr
      (fun z hz => hv z hz) (hv y hy)
  have hsχ : ContMDiffOn I4 I4 ∞ χ A := by
    intro x _
    exact ((inverse_smooth x.val x.property).contMDiffAt.comp x
      (contMDiff_subtype_val (U := U)).contMDiffAt).contMDiffWithinAt
  obtain ⟨C,hC,hb⟩ := kerr_oblate_chart_component_decay ψ hv
  let E : AsymptoticallyFlatEnd (kerrNewmanMetricField (5/2) 2 0) (kerrNewmanFieldField 2 0) φ := {
    R := 1, ψ := ψ, C := C, R_pos := zero_lt_one
    diffeo := by change IsDiffeoOnto ψ S (ψ '' S); rw [hImg]; exact ⟨χ,hψ,hχ,hl,hr,hsψ,hsχ⟩
    isOpen_image := by change IsOpen (ψ '' S); rwa [hImg]
    equivariant := by
      intro t y hy
      have hsp : spatialRadius (y+t • coordBasis 0)=spatialRadius y := by
        unfold spatialRadius
        rw [time_shift _ _ 1 (by decide),time_shift _ _ 2 (by decide),time_shift _ _ 3 (by decide)]
      have hy' : y+t • coordBasis 0∈S := by change 1<spatialRadius _; rwa [hsp]
      apply Subtype.ext
      rw [hφ,hv _ hy',hv _ hy]
      unfold raw
      rw [hsp]
      ext i; fin_cases i <;> simp [four,coordBasis]
    metric_decay := fun y hy i j => (hb y hy i j).1
    metric_deriv_decay := fun y hy i j k => (hb y hy i j).2 k
    field_decay := by
      intro y hy i j
      have zeroField (x : U) : kerrNewmanFieldField 2 0 x=0 := by
        have hm : kerrNewmanField 2 0 x.val=0 := by ext μ ν; simp [kerrNewmanField,coordPartial,kerrNewmanPotential]
        change matrixBilin (kerrNewmanField 2 0 x.val)=0
        rw [hm]; ext v w; simp [matrixBilin,Matrix.toLinearMap₂'_apply]
      simp [pullbackCoeffs,zeroField,div_nonneg hC (sq_nonneg _)] }
  refine ⟨E,rfl,hImg,?_⟩
  intro y hy
  change ksRadius 2 (ψ y).val = spatialRadius y
  rw [hv y hy]
  exact (raw_data y (zero_lt_one.trans hy)).1

theorem solution :
    let g := kerrNewmanMetricField (5/2) 2 0
    let F := kerrNewmanFieldField 2 0
    let T := kerrNewmanTimeDirection (5/2) 2 0
    ∃ (φ : ℝ → kerrNewmanSpacetime 2 → kerrNewmanSpacetime 2)
      (E : AsymptoticallyFlatEnd g F φ),
      let B := fun R : ℝ => E.ψ '' exteriorRegion R
      let D := domainOfOuterCommunications g T E.region
      let H := futureEventHorizon g T E.region
      let Dinf := domainOfOuterCommunicationsAtInfinity g T B E.R
      let Hinf := futureEventHorizonAtInfinity g T B E.R
      E.R = 1 ∧
      (∀ R, E.R ≤ R → B R = {x : kerrNewmanSpacetime 2 | R < ksRadius 2 x.val}) ∧
      IsStationaryBlackHole g F T φ E ∧ (∀ x, F x = 0) ∧ IsAnalyticBilinField g ∧
      IsNondegenerateHorizon g F H D ∧
      D = {x : kerrNewmanSpacetime 2 | 1 < ksRadius 2 x.val} ∧
      H = {x : kerrNewmanSpacetime 2 | ksRadius 2 x.val = 1} ∧
      (∀ μ a : ℝ, IsKerrNewmanBlackHoleParams μ a 0 → ¬ IsKerrNewmanDOC g F D μ a 0) ∧
      Dinf = {x : kerrNewmanSpacetime 2 | 4 < ksRadius 2 x.val} ∧
      Hinf = {x : kerrNewmanSpacetime 2 | ksRadius 2 x.val = 4} ∧
      IsKerrNewmanDOC g F Dinf (5/2) 2 0 := by
  let g := kerrNewmanMetricField (5/2) 2 0
  let F := kerrNewmanFieldField 2 0
  let T := kerrNewmanTimeDirection (5/2) 2 0
  let A := {x : kerrNewmanSpacetime 2 | 1 < ksRadius 2 x.val}
  have hp : IsKerrNewmanBlackHoleParams (5/2) 2 0 := by norm_num [IsKerrNewmanBlackHoleParams]
  obtain ⟨hlor,hmetric,hfield⟩ := kerrNewman_regularTensors (5/2) 2 0
  obtain ⟨φ,_,hφ,hsym,_⟩ := kerrNewman_stationaryFlatEnd (5/2) 2 0 hp
  obtain ⟨E,hR,hE,hchart⟩ := wide_end φ hφ
  have hT := (kerrNewman_outerHorizon_futureTrapped (5/2) 2 0 hp).1
  obtain ⟨hP,hF⟩ := kerr_inner_horizon_chronology
  have hGH := kerr_inner_horizon_global_hyperbolicity
  obtain ⟨han,hB,hC,hn⟩ := kerr_inner_horizon_geometry
  have hD : domainOfOuterCommunications g T E.region = A := by
    rw [domainOfOuterCommunications,hE,hP]
    exact inter_eq_right.mpr hF
  have hH : futureEventHorizon g T E.region=frontier A := by rw [futureEventHorizon,hE,hP]
  have hmat (y : E4) : kerrNewmanField 2 0 y = 0 := by
    ext μ ν
    simp [kerrNewmanField,coordPartial,kerrNewmanPotential]
  have hzero (x : kerrNewmanSpacetime 2) : F x=0 := by
    change matrixBilin (kerrNewmanField 2 0 x.val)=0
    rw [hmat]
    ext v w
    simp [matrixBilin,Matrix.toLinearMap₂'_apply]
  have hbh : IsStationaryBlackHole g F T φ E :=
    { lorentzian := hlor
      smooth_metric := hmetric
      smooth_field := hfield
      twoForm := by intro x v w; rw [hzero]; simp
      timeOrientation := hT
      electrovac := isElectrovac_of_coordinate_equations (kerrNewmanSpacetime 2)
        (kerrNewmanMetric (5/2) 2 0) (kerrNewmanField 2 0) (kerrNewman_einsteinMaxwell (5/2) 2 0)
      stationary := hsym
      globallyHyperbolic := hD.symm ▸ hGH
      blackHole_nonempty := by rw [blackHoleRegion,hE,hP]; exact hB
      horizon_connected := hH.symm ▸ hC }
  have hnd : IsNondegenerateHorizon g F (futureEventHorizon g T E.region)
      (domainOfOuterCommunications g T E.region) := by
    rw [hH,hD]
    exact hn
  let U := kerrNewmanSpacetime 2
  let B := fun R : ℝ => E.ψ '' exteriorRegion R
  let Aᵣ := fun R : ℝ => {x : U | R < ksRadius 2 x.val}
  have htail (R : ℝ) (hRcut : 1 ≤ R) : B R = Aᵣ R := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      have hy1 : y ∈ exteriorRegion 1 := lt_of_le_of_lt hRcut hy
      change R < ksRadius 2 (E.ψ y).val
      rwa [hchart y hy1]
    · intro hx
      have hwide : x ∈ E.region := by
        rw [hE]
        exact lt_of_le_of_lt hRcut hx
      obtain ⟨y,hy,hyx⟩ := hwide
      have hy1 : y ∈ exteriorRegion 1 := by simpa only [hR] using hy
      refine ⟨y,?_,hyx⟩
      change R < spatialRadius y
      rwa [← hchart y hy1, hyx]
  have hBmono : Antitone B := by
    intro R S hRS z hz
    obtain ⟨y,hy,hyz⟩ := hz
    exact ⟨y,lt_of_le_of_lt hRS hy,hyz⟩
  have hInside (R : ℝ) : ∃ S, Aᵣ S ⊆ B R := by
    refine ⟨max 1 R,?_⟩
    rw [← htail (max 1 R) (le_max_left _ _)]
    exact hBmono (le_max_right _ _)
  have hOutside (R : ℝ) : ∃ S, B S ⊆ Aᵣ R := by
    refine ⟨max 1 R,?_⟩
    rw [htail (max 1 R) (le_max_left _ _)]
    intro x hx
    change max (1:ℝ) R < ksRadius 2 x.val at hx
    change R < ksRadius 2 x.val
    exact lt_of_le_of_lt (le_max_right (1:ℝ) R) hx
  obtain ⟨_,hdInf,hhInf,hiso⟩ :=
    (kerrNewman_chronology_at_infinity (5/2) 2 0 E.R hp).2 B hBmono hInside hOutside
  have hb : kerrNewmanOuterRadius (5/2) 2 0 = 4 := by
    unfold kerrNewmanOuterRadius
    rw [show ((5/2:ℝ)^2 - 2^2 - 0^2) = (3/2:ℝ)^2 by norm_num,
      Real.sqrt_sq (by norm_num : 0 ≤ (3/2:ℝ))]
    norm_num
  change domainOfOuterCommunicationsAtInfinity g T B E.R =
    {x : U | kerrNewmanOuterRadius (5/2) 2 0 < ksRadius 2 x.val} at hdInf
  rw [hb] at hdInf hhInf
  refine ⟨φ,E,hR,?_,hbh,hzero,han,hnd,hD,?_,?_,hdInf,hhInf,hiso⟩
  · intro R hRcut
    exact htail R (by simpa only [hR] using hRcut)
  · exact hH.trans (ksRadius_superlevel_frontier 2 1 (by norm_num)).1
  · intro μ a hparams
    rw [hD]
    exact kerr_inner_horizon_shell_not_exterior μ a hparams
