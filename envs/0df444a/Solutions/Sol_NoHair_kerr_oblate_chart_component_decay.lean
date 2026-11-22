-- Prove2me | solution 1 for NoHair.kerr_oblate_chart_component_decay
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T23:33:09.284272+00:00
-- url     : https://prove2.me/submissions/96a3bc0f-85fa-48ee-8e4f-37bbb0ea4fda

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
private theorem four_deriv {t x y z : ℝ → ℝ} {dt dx dy dz s : ℝ}
    (ht : HasDerivAt t dt s) (hx : HasDerivAt x dx s) (hy : HasDerivAt y dy s) (hz : HasDerivAt z dz s) :
    HasDerivAt (fun s => four (t s) (x s) (y s) (z s)) (four dt dx dy dz) s := by
  have h : HasDerivAt (fun s => (![t s,x s,y s,z s] : Fin 4 → ℝ)) ![dt,dx,dy,dz] s := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact ht
    · exact hx
    · exact hy
    · exact hz
  exact (PiLp.hasFDerivAt_toLp (𝕜 := ℝ) 2 _).comp_hasDerivAt s h

private def normCoords (y : E4) := four (1/spatialRadius y) (y 1/spatialRadius y)
  (y 2/spatialRadius y) (y 3/spatialRadius y)
private def rate (z v : E4) := z 1*v 1+z 2*v 2+z 3*v 3
private def ang (z v : E4) (i : Fin 4) := v i-z i*rate z v
private def tangent (z v : E4) := four (-(z 0)*rate z v) (ang z v 1) (ang z v 2) (ang z v 3)
private def bend (z v : E4) := four 0 (-(2*ang z v 2)) (2*ang z v 1) 0
private def jac (z v : E4) := v+z 0 • bend z v
private def eta (v w : E4) : ℝ := -(v 0*w 0)+v 1*w 1+v 2*w 2+v 3*w 3
private def ell (z v : E4) : ℝ := v 0+rate z v
private def amp (z : E4) : ℝ := 5/(1+4*(z 0)^2*(z 3)^2)
private def oblateCorrection (i j : Fin 4) (z : E4) : ℝ :=
  let v := coordBasis i
  let w := coordBasis j
  eta (bend z v) w + eta v (bend z w) + z 0*eta (bend z v) (bend z w) +
    amp z * ell z (jac z v) * ell z (jac z w)

private theorem eta_basis (i j : Fin 4) : eta (coordBasis i) (coordBasis j)=minkowski i j := by
  fin_cases i <;> fin_cases j <;> simp [eta,coordBasis,minkowski]

private theorem resid_smooth (i j : Fin 4) : ContDiff ℝ ∞ (oblateCorrection i j) := by
  have hn (z : E4) : 1+4*(z 0)^2*(z 3)^2 ≠ 0 := by positivity
  unfold oblateCorrection amp ell eta jac bend ang rate four
  simp only [PiLp.add_apply,PiLp.smul_apply,WithLp.ofLp_toLp,Matrix.cons_val,smul_eq_mul]
  fun_prop (disch := exact hn _)

private def line (y v : E4) (s : ℝ) := y+s • v
private theorem line_zero (y v : E4) : line y v 0=y := by simp [line]
private theorem line_deriv (y v : E4) : HasDerivAt (line y v) v 0 := by
  change HasDerivAt (fun s : ℝ => y+s • v) v 0
  simpa only [id_eq,one_smul] using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add y

private theorem along (f : E4 → ℝ) (y v : E4) (hf : DifferentiableAt ℝ f y) :
    HasDerivAt (fun s => f (line y v s)) (fderiv ℝ f y v) 0 := by
  have hh : HasFDerivAt f (fderiv ℝ f y) (line y v 0) := by rw [line_zero]; exact hf.hasFDerivAt
  exact hh.comp_hasDerivAt 0 (line_deriv y v)

private theorem chart_deriv (y v : E4) (hy : 0 < spatialRadius y) :
    HasDerivAt (fun s => normCoords (line y v s))
        ((normCoords y) 0 • tangent (normCoords y) v) 0 ∧
      HasDerivAt (fun s => raw (line y v s)) (jac (normCoords y) v) 0 := by
  let L := line y v
  let r := spatialRadius y
  let z := normCoords y
  have hz : L 0=y := line_zero y v
  have hd (i : Fin 4) : HasDerivAt (fun s => L s i) (v i) 0 :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp_hasDerivAt 0 (line_deriv y v)
  have hn : (L 0 1)^2+(L 0 2)^2+(L 0 3)^2 ≠ 0 := by rw [hz,← radius_sq]; positivity
  have hsum := (((hd 1).pow 2).add ((hd 2).pow 2)).add ((hd 3).pow 2)
  have hr : HasDerivAt (fun s => spatialRadius (L s)) (rate z v) 0 := by
    apply (hsum.sqrt hn).congr_deriv
    simp only [Pi.add_apply,Pi.pow_apply,hz]
    change _ / (2*spatialRadius y) = rate z v
    simp [rate,z,normCoords,four]
    field_simp [hy.ne'] <;> ring
  have hn' : spatialRadius (L 0) ≠ 0 := by rw [hz]; exact hy.ne'
  have hi : HasDerivAt (fun s => 1/spatialRadius (L s)) (z 0*(-(z 0)*rate z v)) 0 := by
    apply ((hasDerivAt_const (0:ℝ) 1).div hr hn').congr_deriv
    rw [hz]
    change (0*spatialRadius y-1*rate z v)/spatialRadius y^2 = (1/spatialRadius y)*(-(1/spatialRadius y)*rate z v)
    ring
  have ha (i : Fin 4) (h : i≠0) : HasDerivAt (fun s => L s i/spatialRadius (L s)) (z 0*ang z v i) 0 := by
    apply ((hd i).div hr hn').congr_deriv
    rw [hz]
    have zi : z i=y i/spatialRadius y := by fin_cases i <;> simp_all [z,normCoords,four]
    change _ = (1/spatialRadius y)*(v i-z i*rate z v)
    rw [zi]; field_simp [hy.ne'] <;> ring
  constructor
  · apply (four_deriv hi (ha 1 (by decide)) (ha 2 (by decide)) (ha 3 (by decide))).congr_deriv
    ext i; fin_cases i <;> rfl
  · apply (four_deriv (hd 0) ((hd 1).sub ((ha 2 (by decide)).const_mul 2))
      ((hd 2).add ((ha 1 (by decide)).const_mul 2)) (hd 3)).congr_deriv
    ext i; fin_cases i <;> simp [jac,bend,four,smul_eq_mul] <;> ring

private theorem chart_derivative (ψ : E4 → kerrNewmanSpacetime 2)
    (hψ : ∀ y ∈ exteriorRegion 1, (ψ y).val=raw y) (y : E4) (hy : y∈exteriorRegion 1) (v : E4) :
    mfderiv I4 I4 ψ y v=jac (normCoords y) v := by
  let U := kerrNewmanSpacetime 2
  have hr : 0 < spatialRadius y := zero_lt_one.trans hy
  have hS : IsOpen (exteriorRegion 1) := isOpen_lt continuous_const (by unfold spatialRadius; fun_prop)
  have he : ((Subtype.val : U → E4) ∘ ψ) =ᶠ[𝓝 y] raw := by
    filter_upwards [hS.mem_nhds hy] with w hw
    exact hψ w hw
  have hs : ContMDiffAt I4 I4 ∞ ψ y := by
    apply ContMDiffWithinAt.contMDiffAt (s := exteriorRegion 1) _ (hS.mem_nhds hy)
    apply (ContMDiffWithinAt.subtypeVal_comp_iff U ψ (exteriorRegion 1) y).mp
    exact (raw_smooth y hr).contMDiffAt.contMDiffWithinAt.congr (fun w hw => hψ w hw) (hψ y hy)
  have hval : ContMDiff I4 I4 ∞ (Subtype.val : U → E4) := contMDiff_subtype_val
  have hc := mfderiv_comp y (hval.mdifferentiableAt (by simp) (x := ψ y)) (hs.mdifferentiableAt (by simp))
  have hinc : (mfderiv I4 I4 (Subtype.val : U → E4) (ψ y) : E4 →L[ℝ] E4) =
      ContinuousLinearMap.id ℝ E4 := mfderiv_extChartAt_self (I := I4) (x := ψ y)
  rw [hinc] at hc
  change mfderiv I4 I4 ((Subtype.val : U → E4) ∘ ψ) y=(mfderiv I4 I4 ψ y : E4 →L[ℝ] E4) at hc
  rw [← hc,mfderiv_eq_fderiv,he.fderiv_eq]
  have h := (raw_smooth y hr).differentiableAt (by simp)
  have hraw : HasFDerivAt raw (fderiv ℝ raw y) (line y v 0) := by rw [line_zero]; exact h.hasFDerivAt
  exact (hraw.comp_hasDerivAt 0 (line_deriv y v)).unique (chart_deriv y v hr).2

private theorem metric_entries (x : kerrNewmanSpacetime 2) (v w : E4) :
    kerrNewmanMetricField (5/2) 2 0 x v w = eta v w +
      ksProfile (5/2) 2 0 x.val * (v 0+ksNull 2 x.val 1*v 1+ksNull 2 x.val 2*v 2+ksNull 2 x.val 3*v 3)*
        (w 0+ksNull 2 x.val 1*w 1+ksNull 2 x.val 2*w 2+ksNull 2 x.val 3*w 3) := by
  change Matrix.toLinearMap₂' ℝ (kerrNewmanMetric (5/2) 2 0 x.val) (WithLp.ofLp v) (WithLp.ofLp w) = _
  simp only [Matrix.toLinearMap₂'_apply,smul_eq_mul,kerrNewmanMetric,Fin.sum_univ_four,ksNull_zero]
  simp [minkowski,eta] <;> ring

private theorem coefficients (ψ : E4 → kerrNewmanSpacetime 2) (hψ : ∀ y∈exteriorRegion 1, (ψ y).val=raw y)
    (y : E4) (hy : y∈exteriorRegion 1) (i j : Fin 4) :
    pullbackCoeffs (kerrNewmanMetricField (5/2) 2 0) ψ y i j =
      minkowski i j+(normCoords y) 0*oblateCorrection i j (normCoords y) := by
  let z := normCoords y
  let r := spatialRadius y
  have hr : 0<r := zero_lt_one.trans hy
  obtain ⟨hR,hK⟩ := raw_data y hr
  have hpos : 0<ksRadius 2 (raw y) := hR.symm ▸ hr
  have hF : ksProfile (5/2) 2 0 (raw y)=z 0*amp z := by
    rw [profile_eq _ _ _ _ hpos]
    unfold fA Wf
    rw [hR,hK]
    change (2*(5/2)*r-0^2)*(1/(r^2+2^2*(y 3/r)^2))=(1/r)*(5/(1+4*(1/r)^2*(y 3/r)^2))
    have h1 : r^2+2^2*(y 3/r)^2 ≠ 0 := by positivity
    have h2 : 1+4*(1/r)^2*(y 3/r)^2 ≠ 0 := by positivity
    field_simp [h1,h2,hr.ne'] <;> ring
  let v := coordBasis i
  let w := coordBasis j
  have fact (q : E4) : q 0+ksNull 2 (raw y) 1*q 1+ksNull 2 (raw y) 2*q 2+ksNull 2 (raw y) 3*q 3=ell z q := by
    rw [hK]; dsimp [ell,rate,z,normCoords,four]; ring
  unfold pullbackCoeffs
  rw [chart_derivative ψ hψ y hy,chart_derivative ψ hψ y hy,metric_entries,hψ y hy,hF,fact,fact,← eta_basis]
  change eta (jac z v) (jac z w) + z 0*amp z*ell z (jac z v)*ell z (jac z w)=eta v w+z 0*oblateCorrection i j z
  unfold oblateCorrection
  change _=eta v w+z 0*(eta (bend z v) w+eta v (bend z w)+z 0*eta (bend z v) (bend z w)+amp z*ell z (jac z v)*ell z (jac z w))
  simp only [eta,jac,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
  ring

private def derivResidual (i j k : Fin 4) (z : E4) : ℝ :=
  -rate z (coordBasis k)*oblateCorrection i j z + fderiv ℝ (oblateCorrection i j) z (tangent z (coordBasis k))
private theorem derivResidual_cont (i j k : Fin 4) : Continuous (derivResidual i j k) := by
  have hh := resid_smooth i j
  have ht : Continuous (fun z => tangent z (coordBasis k)) := by
    unfold tangent four ang rate
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi; intro b
    fin_cases b <;> simp only [Matrix.cons_val] <;> fun_prop
  unfold derivResidual
  apply Continuous.add
  · unfold rate; fun_prop
  · exact (hh.continuous_fderiv_apply (by simp)).comp (continuous_id.prodMk ht)

private theorem coeff_partial (ψ : E4 → kerrNewmanSpacetime 2) (hψ : ∀ y∈exteriorRegion 1, (ψ y).val=raw y)
    (y : E4) (hy : y∈exteriorRegion 1) (i j k : Fin 4) :
    coordPartial (fun z => pullbackCoeffs (kerrNewmanMetricField (5/2) 2 0) ψ z i j) k y =
      (normCoords y 0)^2*derivResidual i j k (normCoords y) := by
  let z := normCoords y
  let v := coordBasis k
  let P := fun a : E4 => minkowski i j+normCoords a 0*oblateCorrection i j (normCoords a)
  have hr : 0<spatialRadius y := zero_lt_one.trans hy
  have hS : IsOpen (exteriorRegion 1) := isOpen_lt continuous_const (by unfold spatialRadius; fun_prop)
  have he : (fun z => pullbackCoeffs (kerrNewmanMetricField (5/2) 2 0) ψ z i j) =ᶠ[𝓝 y] P := by
    filter_upwards [hS.mem_nhds hy] with w hw; exact coefficients ψ hψ w hw i j
  have hNorm : ContDiffAt ℝ ∞ normCoords y := by
    have hs := spatial_smooth y hr
    have hn := hr.ne'
    apply (contDiffAt_piLp 2).mpr; intro a
    fin_cases a
    · change ContDiffAt ℝ ∞ (fun w => 1/spatialRadius w) y; fun_prop (disch := assumption)
    · change ContDiffAt ℝ ∞ (fun w : E4 => w 1/spatialRadius w) y; fun_prop (disch := assumption)
    · change ContDiffAt ℝ ∞ (fun w : E4 => w 2/spatialRadius w) y; fun_prop (disch := assumption)
    · change ContDiffAt ℝ ∞ (fun w : E4 => w 3/spatialRadius w) y; fun_prop (disch := assumption)
  have hDiff : DifferentiableAt ℝ P y := by
    apply ContDiffAt.differentiableAt (n:=∞) _ (by simp)
    apply ContDiffAt.add contDiffAt_const
    exact (((EuclideanSpace.proj (𝕜:=ℝ) 0).contDiff.contDiffAt.comp y hNorm).mul
      ((resid_smooth i j).contDiffAt.comp y hNorm))
  have hND := (chart_deriv y v hr).1
  have hC := (EuclideanSpace.proj (𝕜 := ℝ) 0).hasFDerivAt.comp_hasDerivAt 0 hND
  have hZ : normCoords (line y v 0)=z := by rw [line_zero]
  have hd := (resid_smooth i j).differentiable (by simp) (normCoords (line y v 0))
  have hRes := hd.hasFDerivAt.comp_hasDerivAt 0 hND
  have hTotal := (hC.mul hRes).const_add (minkowski i j)
  unfold coordPartial
  rw [he.fderiv_eq]
  have H := (along P y v hDiff).unique hTotal
  rw [hZ] at H
  rw [H]
  simp only [map_smul,smul_eq_mul,Function.comp_apply,line_zero]
  change (z 0*(-(z 0)*rate z v))*oblateCorrection i j z+z 0*(z 0*fderiv ℝ (oblateCorrection i j) z (tangent z v))=
    (z 0)^2*(-rate z v*oblateCorrection i j z+fderiv ℝ (oblateCorrection i j) z (tangent z v))
  ring

private theorem uniform_bound {ι : Type*} [Finite ι] (K : Set E4) (hK : IsCompact K) (f : ι → E4 → ℝ)
    (hf : ∀ i, Continuous (f i)) : ∃ C : ℝ, ∀ i z, z∈K → |f i z| ≤ C := by
  classical
  have bounds (i : ι) : BddAbove ((fun z => |f i z|) '' K) := hK.bddAbove_image (hf i).abs.continuousOn
  choose c hc using bounds
  obtain ⟨C,hC⟩ := (Set.finite_range c).bddAbove
  exact ⟨C,fun i z hz => (hc i ⟨z,hz,rfl⟩).trans (hC ⟨i,rfl⟩)⟩

theorem solution (ψ : E4 → kerrNewmanSpacetime 2)
    (hψ : ∀ y ∈ exteriorRegion 1, (ψ y).val = WithLp.toLp 2
      ![y 0, y 1-2*(y 2/spatialRadius y), y 2+2*(y 1/spatialRadius y), y 3]) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ exteriorRegion 1, ∀ i j : Fin 4,
      |pullbackCoeffs (kerrNewmanMetricField (5/2) 2 0) ψ y i j - minkowski i j| ≤ C / spatialRadius y ∧
      ∀ k : Fin 4, |coordPartial (fun z => pullbackCoeffs (kerrNewmanMetricField (5/2) 2 0) ψ z i j) k y| ≤
        C / spatialRadius y ^ 2  := by
  let box : Set (Fin 4 → ℝ) := Icc (fun _ => -1) (fun _ => 1)
  let K : Set E4 := WithLp.toLp 2 '' box
  have hK : IsCompact K := (show IsCompact box from isCompact_Icc).image (PiLp.continuous_toLp 2 _)
  have hmem (y : E4) (hy : y∈exteriorRegion 1) : normCoords y∈K := by
    have hr : 0<spatialRadius y := zero_lt_one.trans hy
    have hq : 0 ≤ 1/spatialRadius y := by positivity
    have hq' : 1/spatialRadius y ≤ 1 := (div_le_iff₀ hr).mpr (by simpa using hy.le)
    have hb (i : Fin 4) (hi : i≠0) : |y i/spatialRadius y| ≤ 1 := by
      rw [abs_div,abs_of_pos hr]
      apply (div_le_iff₀ hr).mpr
      rw [one_mul]
      apply (sq_le_sq₀ (abs_nonneg _) hr.le).mp
      rw [sq_abs,radius_sq]
      fin_cases i <;> simp_all <;> nlinarith [sq_nonneg (y 1),sq_nonneg (y 2),sq_nonneg (y 3)]
    refine ⟨WithLp.ofLp (normCoords y),⟨?_,?_⟩,rfl⟩
    · intro i
      fin_cases i
      · change -1≤1/spatialRadius y; linarith
      all_goals exact (abs_le.mp (hb _ (by decide))).1
    · intro i
      fin_cases i
      · exact hq'
      all_goals exact (abs_le.mp (hb _ (by decide))).2
  obtain ⟨C0,h0⟩ := uniform_bound K hK (fun a : Fin 4 × Fin 4 => oblateCorrection a.1 a.2) (fun a => (resid_smooth _ _).continuous)
  obtain ⟨C1,h1⟩ := uniform_bound K hK (fun a : Fin 4 × Fin 4 × Fin 4 => derivResidual a.1 a.2.1 a.2.2)
    (fun a => derivResidual_cont _ _ _)
  let C := max 0 (max C0 C1)
  refine ⟨C,le_max_left _ _,?_⟩
  intro y hy i j
  have hr : 0<spatialRadius y := zero_lt_one.trans hy
  have hz := hmem y hy
  have hq : 0≤1/spatialRadius y := by positivity
  constructor
  · rw [coefficients ψ hψ y hy i j,add_sub_cancel_left,abs_mul]
    change |1/spatialRadius y| * |oblateCorrection i j (normCoords y)| ≤ C/spatialRadius y
    rw [abs_of_nonneg hq]
    calc
      _ ≤ (1/spatialRadius y)*C := mul_le_mul_of_nonneg_left ((h0 (i,j) _ hz).trans ((le_max_left _ _).trans (le_max_right _ _))) hq
      _ = _ := by ring
  · intro k
    rw [coeff_partial ψ hψ y hy i j k,abs_mul,abs_of_nonneg (sq_nonneg _)]
    change (1/spatialRadius y)^2 * |derivResidual i j k (normCoords y)| ≤ C/spatialRadius y^2
    have hh := mul_le_mul_of_nonneg_left ((h1 (i,j,k) _ hz).trans
      ((le_max_right C0 C1).trans (le_max_right 0 _))) (sq_nonneg (1/spatialRadius y))
    calc
      _ ≤ (1/spatialRadius y)^2*C := hh
      _ = _ := by ring
