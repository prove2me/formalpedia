-- Prove2me | solution 1 for NoHair.spatial_harmonic_strong_maximum_three
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T10:29:32.56443+00:00
-- url     : https://prove2.me/submissions/378e062d-b8fc-475f-b059-28094354985a

import Theorems.Thm_NoHair_spatial_gaussian_annulus_barrier
import Theorems.Thm_NoHair_spatial_laplacian_nonpositive_at_maximum
import Definitions.Def_NoHair_staticHorizonGeometry

open NoHair Set Filter
open scoped ContDiff Manifold Topology

noncomputable section

open scoped Matrix

private abbrev X := ADMPoint
private abbrev I := Fin 3
private abbrev Mat := Matrix I I ℝ
private noncomputable abbrev pd := spatialADMPartial
private noncomputable abbrev bvec (i : I) : X := EuclideanSpace.single i 1

private def lap (h : X → Mat) (f : X → ℝ) (x : X) :=
  ∑ i : I, ∑ j : I, (h x)⁻¹ i j*staticSpatialHessian f h i j x

private lemma pd_lin {f b : X → ℝ} {x : X} (df : DifferentiableAt ℝ f x)
    (db : DifferentiableAt ℝ b x) (ε : ℝ) (i : I) :
    pd i (fun t => f t + ε*b t) x = pd i f x+ε*pd i b x := by
  have d := (df.hasFDerivAt.add (db.hasFDerivAt.const_mul ε)).fderiv
  change fderiv ℝ (fun t => f t+ε*b t) x=_ at d
  unfold pd spatialADMPartial
  rw [d]; rfl

private lemma lap_lin {f b : X → ℝ} {W : Set X} (ow : IsOpen W)
    (cf : ContDiffOn ℝ ∞ f W) (cb : ContDiff ℝ ∞ b) (ε : ℝ) (h : X → Mat) (x : X) (hx : x∈W) :
    lap h (fun t => f t+ε*b t) x = lap h f x + ε*lap h b x := by
  let F := fun t => f t+ε*b t
  have fx {t : X} (ht : t∈W) := cf.contDiffAt (ow.mem_nhds ht)
  have d (t : X) (ht : t∈W) (i : I) : pd i F t = pd i f t+ε*pd i b t :=
    pd_lin ((fx ht).differentiableAt (by simp)) (cb.differentiable (by simp) t) ε i
  have pdD {g : X → ℝ} (c : ContDiffAt ℝ ∞ g x) (i : I) : DifferentiableAt ℝ (pd i g) x :=
    ((c.fderiv_right (m:=∞) (by simp)).clm_apply (contDiffAt_const (c:=bvec i))).differentiableAt (by simp)
  have dd (i j : I) : pd i (pd j F) x=pd i (pd j f) x+ε*pd i (pd j b) x := by
    have ev : pd j F =ᶠ[𝓝 x] (fun t => pd j f t+ε*pd j b t) :=
      (show ∀ᶠ t in 𝓝 x, t∈W from ow.mem_nhds hx).mono fun t ht => d t ht j
    exact (congrArg (fun L : X →L[ℝ] ℝ => L (bvec i)) ev.fderiv_eq).trans
      (pd_lin (pdD (fx hx) j) (pdD cb.contDiffAt j) ε i)
  have H (i j : I) : staticSpatialHessian F h i j x=staticSpatialHessian f h i j x+ε*staticSpatialHessian b h i j x := by
    change pd i (pd j F) x - (∑ k : I, spatialLeviCivita h x k i j*pd k F x) = _
    simp only [dd,d x hx,staticSpatialHessian,pd,Fin.sum_univ_three]; ring
  change lap h F x=_
  simp only [lap,H,Fin.sum_univ_three]; ring

set_option maxHeartbeats 800000 in
theorem solution (W : Set ADMPoint) (f : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (hw : IsOpen W) (hf : ContDiffOn ℝ ∞ f W) (hh : ∀ i j, ContDiffOn ℝ ∞ (fun y => h y i j) W) (hp : ∀ x ∈ W, (h x).PosDef)
    (hc : IsConnected W) (eq : ∀ y ∈ W, (∑ i : Fin 3, ∑ j : Fin 3, (h y)⁻¹ i j * staticSpatialHessian f h i j y) = 0)
    (x : ADMPoint) (hx : x∈W) (mx : ∀ y ∈ W, f y ≤ f x) : ∀ y ∈ W, f y = f x := by
  classical
  let M := f x
  let S := W ∩ f ⁻¹' Ici M
  have ct := hf.continuousOn
  have op : IsOpen S := by
    apply Metric.isOpen_iff.mpr
    intro a ha
    obtain ⟨R,rp,near⟩ := Metric.mem_nhds_iff.mp (hw.mem_nhds ha.1)
    have halfR : Metric.closedBall a (R/2) ⊆ W := fun t ht =>
      near (Metric.mem_ball.mpr ((Metric.mem_closedBall.mp ht).trans_lt (by linarith)))
    refine ⟨R/4,by positivity,?_⟩
    intro y hy
    have ya : dist y a < R/4 := Metric.mem_ball.mp hy
    have wy : y∈W := near (Metric.mem_ball.mpr (ya.trans (by linarith)))
    refine ⟨wy,?_⟩
    by_contra ny
    have small : f y < M := lt_of_not_ge ny
    let K := Metric.closedBall a (R/2) ∩ f ⁻¹' Ici M
    have compact : IsCompact K := (ct.mono halfR).upperSemicontinuousOn.isCompact_inter_preimage_Ici (isCompact_closedBall _ _) M
    have ak : a∈K := ⟨Metric.mem_closedBall_self (by positivity),ha.2⟩
    obtain ⟨z,hz,mind⟩ := compact.exists_isMinOn ⟨a,ak⟩ (continuous_id.dist (continuous_const (y:=y))).continuousOn
    let r := dist z y
    have wz := halfR hz.1
    have maximum : f z=M := le_antisymm (mx z wz) hz.2
    have rpos : 0<r := dist_pos.mpr (fun e => small.ne (e ▸ maximum))
    have rle : r≤dist a y := mind ak
    have disk : Metric.closedBall y r ⊆ Metric.closedBall a (R/2) := by
      intro t ht
      apply Metric.mem_closedBall.mpr
      have dt := dist_triangle t y a
      have rr := Metric.mem_closedBall.mp ht
      rw [dist_comm a y] at rle
      linarith only [ya,rle,dt,rr]
    have inW := disk.trans halfR
    have below (t : X) (ht : dist t y < r) : f t < M := by
      by_contra! high
      exact ht.not_ge (mind (show t∈K from ⟨disk (Metric.mem_closedBall.mpr ht.le),high⟩))
    obtain ⟨α,ap,cb,lb,dnz⟩ := spatial_gaussian_annulus_barrier W h hw hh hp y r rpos inW
    let b := fun t : X => Real.exp (-α*‖t-y‖^2)-Real.exp (-α*r^2)
    have bzero (t : X) (ht : dist t y=r) : b t=0 := by
      change Real.exp (-α*‖t-y‖^2)-Real.exp (-α*r^2)=0
      rw [←dist_eq_norm,ht,sub_self]
    have bfar (t : X) (ht : r≤dist t y) : b t≤0 := by
      apply sub_nonpos.mpr
      apply Real.exp_le_exp.mpr
      rw [←dist_eq_norm]
      exact mul_le_mul_of_nonpos_left (pow_le_pow_left₀ rpos.le ht 2) (neg_nonpos.mpr ap.le)
    have bone (t : X) : b t≤1 := by
      have e : Real.exp (-α*‖t-y‖^2) ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ap.le) (sq_nonneg _))
      dsimp only [b]
      linarith only [e,Real.exp_pos (-α*r^2)]
    have sph : Metric.sphere y (r/2) ⊆ W := fun t ht => inW (Metric.mem_closedBall.mpr
      ((Metric.mem_sphere.mp ht).le.trans (by linarith)))
    obtain ⟨t₀,ht₀,mf⟩ := (isCompact_sphere y (r/2)).exists_isMaxOn
      (NormedSpace.sphere_nonempty.mpr (by positivity)) (ct.mono sph)
    have gap := below t₀ ((Metric.mem_sphere.mp ht₀).trans_lt (by linarith))
    let ε := (M-f t₀)/2
    have ep : 0<ε := half_pos (sub_pos.mpr gap)
    let F := fun t => f t+ε*b t
    have cf : ContDiffOn ℝ ∞ F W := hf.add (contDiffOn_const.mul cb.contDiffOn)
    let A := Metric.closedBall y r ∩ {t : X | r/2≤dist t y}
    have ac : IsCompact A := (isCompact_closedBall _ _).inter_right (isClosed_le continuous_const (continuous_id.dist continuous_const))
    have outer (t : X) (ht : dist t y=r) : F t≤M := by
      change f t+ε*b t≤M
      rw [bzero t ht,mul_zero,add_zero]
      exact mx t (inW (Metric.mem_closedBall.mpr ht.le))
    have innerBound (t : X) (ht : dist t y=r/2) : F t≤M := by
      have a : f t ≤ f t₀ := mf (Metric.mem_sphere.mpr ht)
      have e := mul_le_mul_of_nonneg_left (bone t) ep.le
      dsimp only [F,ε] at *
      linarith only [a,e,gap]
    have ann (t : X) (ht : t∈A) : F t≤M := by
      by_contra! high
      obtain ⟨m,hm,maxF⟩ := ac.exists_isMaxOn ⟨t,ht⟩ (cf.continuousOn.mono (fun u hu => inW hu.1))
      have large := high.trans_le (maxF ht)
      have hi : dist m y<r := lt_of_le_of_ne (Metric.mem_closedBall.mp hm.1) (fun e => large.not_ge (outer m e))
      have lo : r/2<dist m y := lt_of_le_of_ne hm.2 (fun e => large.not_ge (innerBound m e.symm))
      have localF : IsLocalMax F m := by
        filter_upwards [(isOpen_lt continuous_const (continuous_id.dist (continuous_const (y:=y)))).mem_nhds lo,
          Metric.isOpen_ball.mem_nhds (Metric.mem_ball.mpr hi)] with u u₁ u₂
        exact maxF ⟨Metric.mem_closedBall.mpr (Metric.mem_ball.mp u₂).le,u₁.le⟩
      have wm := inW hm.1
      have neg := spatial_laplacian_nonpositive_at_maximum W F h hw cf m wm (hp m wm) localF
      change lap h F m≤0 at neg
      have val : lap h F m=lap h f m+ε*lap h b m := lap_lin hw hf cb ε h m wm
      have z0 : lap h f m=0 := eq m wm
      have pos : 0<lap h b m := lb m lo.le hi.le
      rw [val,z0,zero_add] at neg
      exact (mul_pos ep pos).not_ge neg
    have Fz : F z=M := by dsimp only [F]; rw [bzero z rfl,mul_zero,add_zero,maximum]
    have mz : IsLocalMax F z := by
      have innerN : r/2<dist z y := by change r/2<r; linarith
      filter_upwards [hw.mem_nhds wz,(isOpen_lt continuous_const (continuous_id.dist (continuous_const (y:=y)))).mem_nhds innerN]
        with t wt rt
      rw [Fz]
      by_cases out : dist t y≤r
      · exact ann t ⟨Metric.mem_closedBall.mpr out,rt.le⟩
      · exact (add_le_of_nonpos_right (mul_nonpos_of_nonneg_of_nonpos ep.le (bfar t (le_of_not_ge out)))).trans (mx t wt)
    have fm : IsLocalMax f z := by
      filter_upwards [hw.mem_nhds wz] with t wt
      rw [maximum]; exact mx t wt
    have zero := ((hf.contDiffAt (hw.mem_nhds wz)).differentiableAt (by simp)).hasFDerivAt.add
      ((cb.differentiable (by simp) z).hasFDerivAt.const_mul ε)
    have dF := zero.fderiv
    change fderiv ℝ F z = fderiv ℝ f z + ε • fderiv ℝ b z at dF
    rw [mz.fderiv_eq_zero,fm.fderiv_eq_zero,zero_add] at dF
    exact dnz z rfl ((smul_eq_zero.mp dF.symm).resolve_left ep.ne')
  let U := W ∩ f ⁻¹' Iio M
  have uopen : IsOpen U := ct.isOpen_inter_preimage hw isOpen_Iio
  have dis : Disjoint S U := Set.disjoint_left.mpr fun y hS hU => (not_lt_of_ge (show M ≤ f y from hS.2)) (show f y < M from hU.2)
  have cover : W⊆S∪U := fun y hy => by
    by_cases t : f y<M
    · exact Or.inr ⟨hy,t⟩
    · exact Or.inl ⟨hy,le_of_not_gt t⟩
  have allS := hc.2.subset_left_of_subset_union op uopen dis cover ⟨x,hx,hx,(show f x ≤ f x from le_rfl)⟩
  exact fun y hy => le_antisymm (mx y hy) (allS hy).2
