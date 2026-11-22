-- Prove2me | solution 1 for NoHair.kerr_inner_horizon_flat_end
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T23:28:05.44576+00:00
-- url     : https://prove2.me/submissions/47dd5223-335f-4707-8e63-e1d41c105206

import Theorems.Thm_NoHair_kerr_oblate_chart_component_decay
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

theorem solution (φ : ℝ → kerrNewmanSpacetime 2 → kerrNewmanSpacetime 2)
    (hφ : ∀ s x, (φ s x).val = x.val+s • coordBasis 0) :
    ∃ E : AsymptoticallyFlatEnd (kerrNewmanMetricField (5/2) 2 0) (kerrNewmanFieldField 2 0) φ,
      E.region = {x : kerrNewmanSpacetime 2 | 1 < ksRadius 2 x.val}  := by
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
  exact ⟨E,hImg⟩
