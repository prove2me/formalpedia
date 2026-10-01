-- Prove2me | solution 1 for NonsmoothNewton.Local.newton_local_order
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T12:58:13.476316+00:00
-- url     : https://prove2.me/submissions/e814b4c3-377a-48d0-99ca-41833cb917d4

import Mathlib
import Definitions.Def_NonsmoothNewton_Local_IsNewtonRun
import Definitions.Def_NonsmoothNewton_Local_SemismoothAt
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
import Definitions.Def_NonsmoothNewton_Local_dirDeriv
import Theorems.Thm_NonsmoothNewton_Shared_isCompact_clarkeJac
import Theorems.Thm_NonsmoothNewton_Shared_exists_local_clarkeJac_subset_thickening

open Filter Topology Set MeasureTheory Module
open NonsmoothNewton.Shared NonsmoothNewton.Local

namespace NonsmoothHelpers

private theorem scalar_slope_bound {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    (f : E → G) {K : NNReal} (hf : LipschitzWith K f)
    (x h : E) (R C : ℝ) (ell : G →L[ℝ] ℝ)
    (hbound : ∀ y,dist y x < R → DifferentiableAt ℝ f y → ell (fderiv ℝ f y h) ≤ C)
    (t : ℝ) (ht : 0 < t) (htR : t*‖h‖ < R) :
    ell (f (x+t • h)-f x) ≤ t*C := by
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  let μ : Measure E := (Basis.ofVectorSpace ℝ E).addHaar
  let M : ℝ →L[ℝ] E := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) h
  have hd : ∀ᵐ y ∂μ,DifferentiableAt ℝ f y := hf.ae_differentiableAt
  have hline : ∀ᵐ y ∂μ,∀ᵐ s : ℝ,DifferentiableAt ℝ f (y+s • h) := by
    simpa [M] using (ae_ae_add_linearMap_mem_iff M.toLinearMap volume μ
      (measurableSet_of_differentiableAt ℝ f)).mpr hd
  have hev : ∀ᵐ y ∂μ,R-t*‖h‖ ≤ dist y x ∨ ell (f (y+t • h)-f y) ≤ t*C := by
    filter_upwards [hline] with y hy
    by_cases hnear : dist y x < R-t*‖h‖
    · right
      let g : ℝ → ℝ := fun s => ell (f (y+s • h))
      have hglip : LipschitzWith (‖ell‖₊ * (K * ‖M‖₊)) g := by
        simpa [g,M,Function.comp_def] using ell.lipschitz.comp (hf.comp ((LipschitzWith.const y).add M.lipschitz))
      have hac : AbsolutelyContinuousOnInterval g 0 t := hglip.lipschitzOnWith.absolutelyContinuousOnInterval
      have hderiv : ∀ᵐ s ∂(volume.restrict (Icc 0 t)),deriv g s ≤ C := by
        filter_upwards [ae_restrict_of_ae hy,ae_restrict_mem measurableSet_Icc] with s hs hst
        have hmem : dist (y+s • h) x < R := by
          rw [dist_eq_norm]
          have hid : y+s • h-x=(y-x)+s • h := by abel
          rw [hid]
          have hnorm : ‖s • h‖ ≤ t*‖h‖ := by
            rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hst.1]
            exact mul_le_mul_of_nonneg_right hst.2 (norm_nonneg h)
          have hn := norm_add_le (y-x) (s • h)
          rw [← dist_eq_norm] at hn
          linarith
        have hh : HasDerivAt (fun a : ℝ => y+a • h) h s := by
          simpa using ((hasDerivAt_id s).smul_const h).const_add y
        have hgf : HasDerivAt g (ell (fderiv ℝ f (y+s • h) h)) s :=
          ell.hasFDerivAt.comp_hasDerivAt s (hs.hasFDerivAt.comp_hasDerivAt s hh)
        rw [hgf.deriv]
        exact hbound (y+s • h) hmem hs
      have hi := intervalIntegral.integral_mono_ae_restrict ht.le hac.intervalIntegrable_deriv
        (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => C) volume 0 t) hderiv
      rw [hac.integral_deriv_eq_sub,intervalIntegral.integral_const] at hi
      simpa [g,map_sub,mul_comm] using hi
    · exact Or.inl (le_of_not_gt hnear)
  have hc : IsClosed {y : E | R-t*‖h‖ ≤ dist y x ∨ ell (f (y+t • h)-f y) ≤ t*C} := by
    exact (isClosed_le continuous_const (continuous_id.dist continuous_const)).union
      (isClosed_le (ell.continuous.comp ((hf.continuous.comp (by fun_prop)).sub hf.continuous)) continuous_const)
  have hx := hc.closure_subset (μ.dense_of_ae hev x)
  simp only [mem_setOf_eq,dist_self] at hx
  rcases hx with hx | hx
  · linarith
  · exact hx



private theorem fderiv_mem_clarke {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : E → G) (x : E) (hd : DifferentiableAt ℝ f x) : fderiv ℝ f x ∈ clarkeJac f x := by
  apply subset_convexHull ℝ (bJac f x)
  exact ⟨fun _ : ℕ => x,tendsto_const_nhds,fun _ => hd,tendsto_const_nhds⟩

private theorem local_scalar_slope_bound {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    (f : E → G) (hf : LocallyLipschitz f) (x h : E) (R C : ℝ) (hR : 0 < R)
    (ell : G →L[ℝ] ℝ)
    (hbound : ∀ y,dist y x < R → ∀ V ∈ clarkeJac f y,ell (V h) ≤ C) :
    ∃ δ > 0,∀ t : ℝ,0 < t → t < δ → ell (f (x+t • h)-f x) ≤ t*C := by
  obtain ⟨K,U,hU,hLip⟩ := hf x
  obtain ⟨d,hd,hdU⟩ := Metric.mem_nhds_iff.mp hU
  obtain ⟨g,hg,heq⟩ := hLip.extend_finite_dimension
  let R' := min d R
  have hR' : 0 < R' := lt_min hd hR
  have hsame : ∀ y,dist y x < R' → f =ᶠ[𝓝 y] g := by
    intro y hy
    have hyball : y ∈ Metric.ball x d := hy.trans_le (min_le_left _ _)
    exact Filter.Eventually.mono (Metric.isOpen_ball.mem_nhds hyball) fun z hz => heq (hdU hz)
  have hgBound : ∀ y,dist y x < R' → DifferentiableAt ℝ g y → ell (fderiv ℝ g y h) ≤ C := by
    intro y hy hdiff
    have hdifff : DifferentiableAt ℝ f y := hdiff.congr_of_eventuallyEq (hsame y hy)
    rw [← (hsame y hy).fderiv_eq]
    exact hbound y (hy.trans_le (min_le_right _ _)) _ (fderiv_mem_clarke f y hdifff)
  refine ⟨R'/(‖h‖+1),by positivity,?_⟩
  intro t ht htd
  have htR : t*‖h‖ < R' := by
    have hh := (lt_div_iff₀ (show 0 < ‖h‖+1 by positivity)).mp htd
    nlinarith [norm_nonneg h]
  have hxx : f x=g x := (hsame x (by simpa using hR')).self_of_nhds
  have hxt : f (x+t • h)=g (x+t • h) := by
    apply (hsame (x+t • h) _).self_of_nhds
    simpa [dist_eq_norm,norm_smul,abs_of_pos ht] using htR
  rw [hxx,hxt]
  exact scalar_slope_bound g hg x h R' C ell hgBound t ht htR



theorem directional_in_clarke {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    (f : E → G) (hf : LocallyLipschitz f) (x h : E) (d : G) (hd : HasDirDerivAt f x h d) :
    ∃ V ∈ clarkeJac f x,d=V h := by
  let ev : (E →L[ℝ] G) →L[ℝ] G := ContinuousLinearMap.apply ℝ G h
  let S : Set G := ev '' clarkeJac f x
  have hc : IsCompact S := (isCompact_clarkeJac f hf x).image ev.continuous
  have hv : Convex ℝ S := (convex_convexHull ℝ (bJac f x)).linear_image ev.toLinearMap
  suffices hdS : d ∈ S by
    obtain ⟨V,hV,hVe⟩ := hdS
    exact ⟨V,hV,hVe.symm⟩
  by_contra hnot
  obtain ⟨ell,u,hlo,hhi⟩ := geometric_hahn_banach_closed_point hv hc.isClosed hnot
  let A := ‖ell‖+1
  let B := ‖h‖+1
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  let eps := (ell d-u)/(2*A*B)
  have heps : 0 < eps := by dsimp [eps]; positivity
  obtain ⟨R,hR,hnear⟩ := exists_local_clarkeJac_subset_thickening f hf x heps
  have hbound : ∀ y,dist y x < R → ∀ V ∈ clarkeJac f y,ell (V h) ≤ (u+ell d)/2 := by
    intro y hy V hV
    obtain ⟨W,hW,hVW⟩ := Metric.mem_thickening_iff.mp (hnear y hy hV)
    have hWb : ell (W h) < u := hlo (W h) ⟨W,hW,rfl⟩
    have hdiff : ‖ell (V h-W h)‖ ≤ (ell d-u)/2 := by
      calc
        ‖ell (V h-W h)‖ ≤ ‖ell‖*‖V h-W h‖ := ell.le_opNorm _
        _ ≤ A*(eps*B) := by
          apply mul_le_mul (by dsimp [A]; linarith) _ (norm_nonneg _) hA.le
          change ‖(V-W) h‖ ≤ eps*B
          apply ((V-W).le_opNorm h).trans
          rw [dist_eq_norm] at hVW
          exact mul_le_mul hVW.le (by dsimp [B]; linarith) (norm_nonneg h) heps.le
        _ = (ell d-u)/2 := by dsimp [eps]; field_simp
    have hab := (le_abs_self (ell (V h-W h))).trans hdiff
    rw [map_sub] at hab
    linarith
  obtain ⟨δ,hδ,hsl⟩ := local_scalar_slope_bound f hf x h R ((u+ell d)/2) hR ell hbound
  have hlim : Tendsto (fun t : ℝ => ell (t⁻¹ • (f (x+t • h)-f x))) (𝓝[>] 0) (𝓝 (ell d)) :=
    ell.continuous.continuousAt.tendsto.comp hd
  have hevent : ∀ᶠ t : ℝ in 𝓝[>] 0,ell (t⁻¹ • (f (x+t • h)-f x)) ≤ (u+ell d)/2 := by
    filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds] with t ht htd
    have hh := hsl t ht htd
    rw [map_smul,smul_eq_mul]
    have hh' : ell (f (x+t • h)-f x)/t ≤ (u+ell d)/2 :=
      (div_le_iff₀ ht).mpr (by simpa [mul_comm] using hh)
    simpa [div_eq_mul_inv,mul_comm] using hh'
  have hh := le_of_tendsto hlim hevent
  linarith



theorem directional_exists_value {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : E → G) (x h : E) (hd : ∃ d,HasDirDerivAt f x h d) :
    HasDirDerivAt f x h (dirDeriv f x h) := by
  obtain ⟨d,hd⟩ := hd
  have he : dirDeriv f x h=d := hd.limUnder_eq
  rwa [he]

theorem directional_lipschitz {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : E → G) (hf : LocallyLipschitz f) (x : E)
    (hdir : ∀ h,∃ d,HasDirDerivAt f x h d) :
    ∃ K : NNReal,LipschitzWith K (fun h => dirDeriv f x h) := by
  obtain ⟨K,U,hU,hLip⟩ := hf x
  refine ⟨K,LipschitzWith.of_dist_le_mul fun h v => ?_⟩
  have hdh := directional_exists_value f x h (hdir h)
  have hdv := directional_exists_value f x v (hdir v)
  have hline (a : E) : Tendsto (fun t : ℝ => x+t • a) (𝓝[>] 0) (𝓝 x) := by
    have hc : Continuous (fun t : ℝ => x+t • a) := by fun_prop
    simpa using (hc.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ t : ℝ in 𝓝[>] 0,
      dist (t⁻¹ • (f (x+t • h)-f x)) (t⁻¹ • (f (x+t • v)-f x)) ≤ K*dist h v := by
    filter_upwards [self_mem_nhdsWithin,(hline h).eventually hU,(hline v).eventually hU] with t ht hh hv
    change 0 < t at ht
    have hl := hLip.dist_le_mul (x+t • h) hh (x+t • v) hv
    simp only [dist_eq_norm,add_sub_add_left_eq_sub,← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos ht] at hl
    rw [dist_eq_norm,← smul_sub,sub_sub_sub_cancel_right,norm_smul,
      Real.norm_eq_abs,abs_inv,abs_of_pos ht]
    calc
      t⁻¹*‖f (x+t • h)-f (x+t • v)‖ ≤ t⁻¹*(K*(t*‖h-v‖)) :=
        mul_le_mul_of_nonneg_left hl (inv_nonneg.mpr ht.le)
      _ = K*dist h v := by rw [dist_eq_norm]; field_simp [ne_of_gt ht]
  exact le_of_tendsto (hdh.dist hdv) hev



private theorem line_directional {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : E → G) (x h : E) (s : ℝ) (d : G)
    (hd : HasDerivAt (fun a : ℝ => f (x+a • h)) d s) :
    HasDirDerivAt f (x+s • h) h d := by
  simpa only [HasDirDerivAt,add_smul,add_assoc] using hd.tendsto_slope_zero_right

private theorem curve_error_bound {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    (f : E → G) (hf : LocallyLipschitz f) (x h : E) (L : G) (eps t : ℝ)
    (heps : 0 ≤ eps) (ht : 0 < t) {K : NNReal}
    (hLip : LipschitzOnWith K (fun s : ℝ => f (x+s • h)) (Icc 0 t))
    (hbound : ∀ s : ℝ,0 < s → s < t → ∀ V ∈ clarkeJac f (x+s • h),‖V h-L‖ ≤ eps) :
    ‖f (x+t • h)-f x-t • L‖ ≤ t*eps := by
  obtain ⟨ell,hell,hellR⟩ := exists_dual_vector'' ℝ (f (x+t • h)-f x-t • L)
  let g : ℝ → ℝ := fun s => ell (f (x+s • h)-s • L)
  let M : ℝ →L[ℝ] G := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) L
  have hglip : LipschitzOnWith (‖ell‖₊*(K+‖M‖₊)) g (Icc 0 t) := by
    simpa [g,M,Function.comp_def] using ell.lipschitz.comp_lipschitzOnWith
      (hLip.sub M.lipschitz.lipschitzOnWith)
  have hac : AbsolutelyContinuousOnInterval g 0 t := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval
    simpa [uIcc_of_le ht.le] using hglip
  have hdiff : ∀ᵐ s : ℝ,s ∈ Icc 0 t → DifferentiableWithinAt ℝ (fun a : ℝ => f (x+a • h)) (Icc 0 t) s :=
    hLip.ae_differentiableWithinAt_of_mem
  have hderiv : ∀ᵐ s ∂(volume.restrict (Icc 0 t)),deriv g s ≤ eps := by
    filter_upwards [ae_restrict_of_ae hdiff,ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae (volume.ae_ne (0 : ℝ)),ae_restrict_of_ae (volume.ae_ne t)] with s hs hst hs0 hstn
    have hspos : 0 < s := lt_of_le_of_ne hst.1 (Ne.symm hs0)
    have hstlt : s < t := lt_of_le_of_ne hst.2 hstn
    have hd := (hs hst).differentiableAt (Icc_mem_nhds hspos hstlt)
    obtain ⟨V,hV,hVe⟩ := directional_in_clarke f hf (x+s • h) h _
      (line_directional f x h s _ hd.hasDerivAt)
    have hnorm : ‖deriv (fun a : ℝ => f (x+a • h)) s-L‖ ≤ eps := by
      rw [hVe]
      exact hbound s hspos hstlt V hV
    have hgderiv : HasDerivAt g (ell (deriv (fun a : ℝ => f (x+a • h)) s-L)) s :=
      ell.hasFDerivAt.comp_hasDerivAt s (hd.hasDerivAt.sub (by simpa using (hasDerivAt_id s).smul_const L))
    rw [hgderiv.deriv]
    exact (le_abs_self _).trans ((ell.le_opNorm _).trans
      ((mul_le_mul hell hnorm (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (one_mul eps)))
  have hi := intervalIntegral.integral_mono_ae_restrict ht.le hac.intervalIntegrable_deriv
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => eps) volume 0 t) hderiv
  rw [hac.integral_deriv_eq_sub,intervalIntegral.integral_const] at hi
  have he : g t-g 0=‖f (x+t • h)-f x-t • L‖ := by
    have hellR' : ell (f (x+t • h)-f x-t • L)=‖f (x+t • h)-f x-t • L‖ := by simpa using hellR
    rw [← hellR']
    dsimp [g]
    rw [← map_sub]
    congr 1
    simp only [zero_smul,add_zero,sub_zero]
    abel
  simpa [he] using hi

theorem clarke_limit_hasDirDeriv {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    (f : E → G) (hf : LocallyLipschitz f) (x h : E) (L : G)
    (hL : ∀ eps > 0,∃ δ > 0,∀ t : ℝ,0 < t → t < δ →
      ∀ V ∈ clarkeJac f (x+t • h),‖V h-L‖ < eps) : HasDirDerivAt f x h L := by
  obtain ⟨K,U,hU,hLip⟩ := hf x
  obtain ⟨d,hd,hdU⟩ := Metric.mem_nhds_iff.mp hU
  let M : ℝ →L[ℝ] E := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) h
  have hlin : LipschitzWith ‖M‖₊ (fun s : ℝ => x+s • h) := by
    simpa [M] using (LipschitzWith.const x).add M.lipschitz
  apply Metric.tendsto_nhds.mpr
  intro eps heps
  obtain ⟨δ,hδ,hV⟩ := hL (eps/2) (by positivity)
  let e := min δ (d/(‖h‖+1))
  have he : 0 < e := by dsimp [e]; positivity
  filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds he).filter_mono nhdsWithin_le_nhds] with t ht hte
  change 0 < t at ht
  have htd : t*‖h‖ < d := by
    have hh := (lt_div_iff₀ (show 0 < ‖h‖+1 by positivity)).mp (hte.trans_le (min_le_right _ _))
    nlinarith
  have hmaps : MapsTo (fun s : ℝ => x+s • h) (Icc 0 t) U := by
    intro s hs
    apply hdU
    change dist (x+s • h) x < d
    rw [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg hs.1]
    exact (mul_le_mul_of_nonneg_right hs.2 (norm_nonneg h)).trans_lt htd
  have hcurve : LipschitzOnWith (K*‖M‖₊) (fun s : ℝ => f (x+s • h)) (Icc 0 t) :=
    hLip.comp hlin.lipschitzOnWith hmaps
  have hres := curve_error_bound f hf x h L (eps/2) t (by positivity) ht hcurve
    (fun s hs hst V hmem => (hV s hs (hst.trans (hte.trans_le (min_le_left _ _))) V hmem).le)
  have hid : t⁻¹ • (f (x+t • h)-f x)-L=t⁻¹ • (f (x+t • h)-f x-t • L) := by
    simp only [smul_sub,smul_smul,inv_mul_cancel₀ (ne_of_gt ht),one_smul]
  rw [dist_eq_norm,hid,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos ht]
  calc
    t⁻¹*‖f (x+t • h)-f x-t • L‖ ≤ t⁻¹*(t*(eps/2)) :=
      mul_le_mul_of_nonneg_left hres (inv_nonneg.mpr ht.le)
    _ = eps/2 := by field_simp [ne_of_gt ht]
    _ < eps := by linarith



theorem directional_zero {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (f : E → G) (x : E) : dirDeriv f x 0=0 := by
  have hd : HasDirDerivAt f x 0 0 := by
    simpa [HasDirDerivAt] using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : G)) (𝓝[>] 0) (𝓝 0))
  exact hd.limUnder_eq

theorem directional_smul {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (f : E → G) (x h : E)
    (hd : ∃ d,HasDirDerivAt f x h d) (a : ℝ) (ha : 0 ≤ a) :
    dirDeriv f x (a • h)=a • dirDeriv f x h := by
  rcases eq_or_lt_of_le ha with rfl | hapos
  · simp [directional_zero]
  have ht : Tendsto (fun t : ℝ => a*t) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : Continuous (fun t : ℝ => a*t) := by fun_prop
      simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact mul_pos hapos ht
  have hl : Tendsto (fun t : ℝ => a • ((a*t)⁻¹ • (f (x+(a*t) • h)-f x)))
      (𝓝[>] 0) (𝓝 (a • dirDeriv f x h)) :=
    tendsto_const_nhds.smul ((directional_exists_value f x h hd).comp ht)
  have hnew : HasDirDerivAt f x (a • h) (a • dirDeriv f x h) := by
    simpa [HasDirDerivAt,smul_smul,mul_inv_rev,mul_comm,mul_left_comm,mul_assoc,ne_of_gt hapos] using hl
  exact hnew.limUnder_eq

theorem semi_directional {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    (f : E → G) (hf : LocallyLipschitz f) (x : E) (hs : SemismoothAt f x) :
    ∀ h,∃ d,HasDirDerivAt f x h d := by
  intro h
  obtain ⟨L,hL⟩ := hs.2 h
  refine ⟨L,clarke_limit_hasDirDeriv f hf x h L ?_⟩
  intro eps heps
  obtain ⟨δ,hδ,hd⟩ := hL eps heps
  exact ⟨δ,hδ,fun t ht htd => hd t h ht htd (by simpa using hδ)⟩

theorem semi_full_limit {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    (f : E → G) (hf : LocallyLipschitz f) (x : E) (hs : SemismoothAt f x) (h : E) :
    ∀ eps > 0,∃ δ > 0,∀ (t : ℝ) (v : E),0 < t → t < δ → ‖v-h‖ < δ →
      ∀ V ∈ clarkeJac f (x+t • v),‖V v-dirDeriv f x h‖ < eps := by
  obtain ⟨L,hL⟩ := hs.2 h
  have hd : HasDirDerivAt f x h L := by
    apply clarke_limit_hasDirDeriv f hf x h L
    intro eps heps
    obtain ⟨δ,hδ,hd⟩ := hL eps heps
    exact ⟨δ,hδ,fun t ht htd => hd t h ht htd (by simpa using hδ)⟩
  have heq : dirDeriv f x h=L := hd.limUnder_eq
  rw [heq]
  exact hL

theorem semi_uniform_residual {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    (f : E → G) (hf : LocallyLipschitz f) (x : E) (hs : SemismoothAt f x) :
    ∀ eps > 0,∃ δ > 0,∀ h : E,‖h‖ < δ → ∀ V ∈ clarkeJac f (x+h),
      ‖V h-dirDeriv f x h‖ ≤ eps*‖h‖ := by
  classical
  intro eps heps
  have hdir := semi_directional f hf x hs
  obtain ⟨K,hK⟩ := directional_lipschitz f hf x hdir
  choose d hd hds using fun h => semi_full_limit f hf x hs h (eps/2) (by positivity)
  let e : E → ℝ := fun h => min (d h) (eps/(4*(K+1)))
  have he : ∀ h,0 < e h := by intro h; exact lt_min (hd h) (by positivity)
  obtain ⟨q,hqsub,hqfin,hqcover⟩ := (isCompact_sphere (0 : E) 1).elim_finite_subcover_image
    (b := Metric.sphere (0 : E) 1) (c := fun h => Metric.ball h (e h))
    (fun _ _ => Metric.isOpen_ball) (fun h hh => mem_biUnion hh (by simpa using he h))
  have hev : ∀ᶠ t : ℝ in 𝓝 0,∀ h ∈ q,‖t‖ < d h := by
    apply hqfin.eventually_all.mpr
    intro h hh
    exact (continuous_norm.tendsto 0).eventually (eventually_lt_nhds (by simpa using hd h))
  obtain ⟨δ,hδ,hdlt⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨δ,hδ,?_⟩
  intro h hh V hV
  by_cases hh0 : h=0
  · simp [hh0,directional_zero]
  let v := ‖h‖⁻¹ • h
  have hn : 0 < ‖h‖ := norm_pos_iff.mpr hh0
  have hv : v ∈ Metric.sphere (0 : E) 1 := by
    simp [v,Metric.mem_sphere,dist_eq_norm,norm_smul,abs_of_pos hn,ne_of_gt hn]
  obtain ⟨w,hwq,hw⟩ := mem_iUnion₂.mp (hqcover hv)
  have hwv : ‖v-w‖ < e w := by simpa [Metric.mem_ball,dist_eq_norm] using hw
  have hball : dist (‖h‖) 0 < δ := by simpa using hh
  have ht : ‖h‖ < d w := by simpa using hdlt hball w hwq
  have hid : ‖h‖ • v=h := by simp [v,smul_smul,ne_of_gt hn]
  have hnear := hds w ‖h‖ v hn ht (hwv.trans_le (min_le_left _ _)) V (by simpa [hid] using hV)
  have hdirnear : ‖dirDeriv f x w-dirDeriv f x v‖ ≤ eps/4 := by
    have hh := hK.dist_le_mul w v
    rw [dist_eq_norm,dist_comm,dist_eq_norm] at hh
    apply hh.trans
    calc
      (K : ℝ)*‖v-w‖ ≤ (K+1)*(eps/(4*(K+1))) :=
        mul_le_mul (by linarith) (hwv.le.trans (min_le_right _ _)) (norm_nonneg _) (by positivity)
      _ = eps/4 := by field_simp
  have hunit : ‖V v-dirDeriv f x v‖ ≤ eps := by
    have hid' : V v-dirDeriv f x v=(V v-dirDeriv f x w)+(dirDeriv f x w-dirDeriv f x v) := by abel
    rw [hid']
    exact (norm_add_le _ _).trans (by linarith)
  have heq : dirDeriv f x h=‖h‖ • dirDeriv f x v := by
    simpa only [hid] using directional_smul f x v (hdir v) ‖h‖ hn.le
  have haction : V h=‖h‖ • V v := by
    calc V h=V (‖h‖ • v) := congrArg V hid.symm
         _=‖h‖ • V v := map_smul V _ _
  rw [heq,haction,← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos hn]
  have hmul := mul_le_mul_of_nonneg_left hunit hn.le
  simpa [hid,mul_comm] using hmul



private theorem exists_ray_lipschitz {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : E → G) (hf : LocallyLipschitz f) (x : E) :
    ∃ r > 0,∀ h : E,‖h‖ < r → ∃ K : NNReal,
      LipschitzOnWith K (fun s : ℝ => f (x+s • h)) (Icc 0 1) := by
  obtain ⟨K,U,hU,hLip⟩ := hf x
  obtain ⟨r,hr,hrU⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨r,hr,?_⟩
  intro h hh
  let M : ℝ →L[ℝ] E := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) h
  have hlin : LipschitzWith ‖M‖₊ (fun s : ℝ => x+s • h) := by
    simpa [M] using (LipschitzWith.const x).add M.lipschitz
  refine ⟨K*‖M‖₊,hLip.comp hlin.lipschitzOnWith ?_⟩
  intro s hs
  apply hrU
  change dist (x+s • h) x < r
  rw [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg hs.1]
  exact (mul_le_of_le_one_left (norm_nonneg h) hs.2).trans_lt hh

theorem semi_remainder {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    (f : E → G) (hf : LocallyLipschitz f) (x : E) (hs : SemismoothAt f x) :
    ∀ eps > 0,∃ δ > 0,∀ h : E,‖h‖ < δ →
      ‖f (x+h)-f x-dirDeriv f x h‖ ≤ eps*‖h‖ := by
  have hdir := semi_directional f hf x hs
  intro eps heps
  obtain ⟨r,hr,hLip⟩ := exists_ray_lipschitz f hf x
  obtain ⟨d,hd,hres⟩ := semi_uniform_residual f hf x hs eps heps
  refine ⟨min r d,lt_min hr hd,?_⟩
  intro h hh
  obtain ⟨K,hK⟩ := hLip h (hh.trans_le (min_le_left _ _))
  have hbd : ∀ s : ℝ,0 < s → s < 1 → ∀ V ∈ clarkeJac f (x+s • h),
      ‖V h-dirDeriv f x h‖ ≤ eps*‖h‖ := by
    intro s hs0 hs1 V hV
    have hsmall : ‖s • h‖ < d := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos hs0]
      exact (mul_le_of_le_one_left (norm_nonneg h) hs1.le).trans_lt (hh.trans_le (min_le_right _ _))
    have hb := hres (s • h) hsmall V hV
    rw [directional_smul f x h (hdir h) s hs0.le,map_smul,← smul_sub,norm_smul,
      norm_smul,Real.norm_eq_abs,abs_of_pos hs0] at hb
    nlinarith
  have hb := curve_error_bound f hf x h (dirDeriv f x h) (eps*‖h‖) 1
    (mul_nonneg heps.le (norm_nonneg h)) (by norm_num) hK hbd
  simpa using hb

theorem porder_remainder {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    (f : E → G) (hf : LocallyLipschitz f) (x : E) (p : ℝ) (hp : 0 < p)
    (hord : POrderSemismoothAt p f x) :
    ∃ C δ : ℝ,0 < δ ∧ ∀ h : E,‖h‖ < δ →
      ‖f (x+h)-f x-dirDeriv f x h‖ ≤ C*‖h‖^(1+p) := by
  have hdir := semi_directional f hf x hord.1
  obtain ⟨C,d,hd,hres⟩ := hord.2
  obtain ⟨r,hr,hLip⟩ := exists_ray_lipschitz f hf x
  let C' := max C 0
  have hC : 0 ≤ C' := le_max_right _ _
  refine ⟨C',min r d,lt_min hr hd,?_⟩
  intro h hh
  obtain ⟨K,hK⟩ := hLip h (hh.trans_le (min_le_left _ _))
  have hbd : ∀ s : ℝ,0 < s → s < 1 → ∀ V ∈ clarkeJac f (x+s • h),
      ‖V h-dirDeriv f x h‖ ≤ C'*‖h‖^(1+p) := by
    intro s hs0 hs1 V hV
    have hsmall : ‖s • h‖ < d := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos hs0]
      exact (mul_le_of_le_one_left (norm_nonneg h) hs1.le).trans_lt (hh.trans_le (min_le_right _ _))
    have hb := hres (s • h) hsmall V hV _ (directional_exists_value f x (s • h) (hdir (s • h)))
    have hb' := hb.trans (mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.rpow_nonneg (norm_nonneg (s • h)) (1+p)))
    change ‖V (s • h)-dirDeriv f x (s • h)‖ ≤ C'*‖s • h‖^(1+p) at hb'
    rw [directional_smul f x h (hdir h) s hs0.le,map_smul,← smul_sub,norm_smul,
      norm_smul,Real.norm_eq_abs,abs_of_pos hs0,Real.mul_rpow hs0.le (norm_nonneg h)] at hb'
    have hpw : s^(1+p) ≤ s := Real.rpow_le_self_of_le_one hs0.le hs1.le (by linarith)
    have hmul := mul_le_mul_of_nonneg_right hpw (mul_nonneg hC (Real.rpow_nonneg (norm_nonneg h) (1+p)))
    nlinarith
  have hb := curve_error_bound f hf x h (dirDeriv f x h) (C'*‖h‖^(1+p)) 1
    (mul_nonneg hC (Real.rpow_nonneg (norm_nonneg h) (1+p))) (by norm_num) hK hbd
  simpa using hb


private theorem inverse_neighborhood {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hF : LocallyLipschitz F)
    (x : EuclideanSpace ℝ (Fin n)) (hns : ∀ V ∈ clarkeJac F x, IsUnit V) :
    ∃ N ∈ 𝓝 x, ∃ C : ℝ, ∀ y ∈ N, ∀ V ∈ clarkeJac F y,
      ∃ W : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n),
        V.comp W = ContinuousLinearMap.id ℝ _ ∧ W.comp V = ContinuousLinearMap.id ℝ _ ∧
        ‖W‖ ≤ C := by
  let R := EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)
  have hc := isCompact_clarkeJac F hF x
  have hi : ContinuousOn (Ring.inverse : R → R) (clarkeJac F x) := by
    intro V hV
    obtain ⟨u,rfl⟩ := hns V hV
    exact (NormedRing.inverse_continuousAt u).continuousWithinAt
  obtain ⟨C,hC⟩ := hc.bddAbove_image hi.norm
  let U : Set R := {V | IsUnit V ∧ ‖Ring.inverse V‖ < C+1}
  have hU : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    intro V hV
    obtain ⟨⟨u,rfl⟩,hu⟩ := hV
    have hh := (NormedRing.inverse_continuousAt u).norm.eventually_lt_const hu
    exact Filter.inter_mem u.nhds hh
  have hsub : clarkeJac F x ⊆ U := by
    intro V hV
    refine ⟨hns V hV,?_⟩
    have hh := hC (Set.mem_image_of_mem (fun V : R => ‖Ring.inverse V‖) hV)
    linarith
  obtain ⟨eps,heps,hth⟩ := hc.exists_thickening_subset_open hU hsub
  obtain ⟨delta,hdelta,hd⟩ := exists_local_clarkeJac_subset_thickening F hF x heps
  refine ⟨Metric.ball x delta,Metric.ball_mem_nhds x hdelta,C+1,?_⟩
  intro y hy V hV
  have hg := hth (hd y hy hV)
  refine ⟨Ring.inverse V,?_,?_,hg.2.le⟩
  · change V*Ring.inverse V=1
    exact Ring.mul_inverse_cancel V hg.1
  · change Ring.inverse V*V=1
    exact Ring.inverse_mul_cancel V hg.1


theorem nonlinear_residual {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    (f : E → G) (hf : LocallyLipschitz f) (x : E) (hs : SemismoothAt f x) :
    ∀ eps > 0,∃ δ > 0,∀ h : E,‖h‖ < δ → ∀ V ∈ clarkeJac f (x+h),
      ‖f (x+h)-f x-V h‖ ≤ eps*‖h‖ := by
  intro eps heps
  obtain ⟨d,hd,hds⟩ := semi_uniform_residual f hf x hs (eps/2) (by positivity)
  obtain ⟨r,hr,hrs⟩ := semi_remainder f hf x hs (eps/2) (by positivity)
  refine ⟨min d r,lt_min hd hr,?_⟩
  intro h hh V hV
  have hv := hds h (hh.trans_le (min_le_left _ _)) V hV
  have hf := hrs h (hh.trans_le (min_le_right _ _))
  have hid : f (x+h)-f x-V h=(f (x+h)-f x-dirDeriv f x h)+(dirDeriv f x h-V h) := by abel
  rw [hid]
  have hn := norm_add_le (f (x+h)-f x-dirDeriv f x h) (dirDeriv f x h-V h)
  rw [norm_sub_rev (dirDeriv f x h) (V h)] at hn
  linarith

theorem porder_nonlinear_residual {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    (f : E → G) (hf : LocallyLipschitz f) (x : E) (p : ℝ) (hp : 0 < p)
    (hord : POrderSemismoothAt p f x) :
    ∃ C δ : ℝ,0 ≤ C ∧ 0 < δ ∧ ∀ h : E,‖h‖ < δ → ∀ V ∈ clarkeJac f (x+h),
      ‖f (x+h)-f x-V h‖ ≤ C*‖h‖^(1+p) := by
  have hdir := semi_directional f hf x hord.1
  obtain ⟨C,d,hd,hds⟩ := hord.2
  obtain ⟨B,r,hr,hrs⟩ := porder_remainder f hf x p hp hord
  refine ⟨max C 0+max B 0,min d r,by positivity,lt_min hd hr,?_⟩
  intro h hh V hV
  have hv := hds h (hh.trans_le (min_le_left _ _)) V hV _
    (directional_exists_value f x h (hdir h))
  have hfb := hrs h (hh.trans_le (min_le_right _ _))
  have hpow := Real.rpow_nonneg (norm_nonneg h) (1+p)
  have hv' := hv.trans (mul_le_mul_of_nonneg_right (le_max_left C 0) hpow)
  have hf' := hfb.trans (mul_le_mul_of_nonneg_right (le_max_left B 0) hpow)
  have hid : f (x+h)-f x-V h=(f (x+h)-f x-dirDeriv f x h)+(dirDeriv f x h-V h) := by abel
  rw [hid]
  have hn := norm_add_le (f (x+h)-f x-dirDeriv f x h) (dirDeriv f x h-V h)
  rw [norm_sub_rev (dirDeriv f x h) (V h)] at hn
  nlinarith

private theorem inverse_ball {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hf : LocallyLipschitz f)
    (x : EuclideanSpace ℝ (Fin n)) (hns : ∀ V ∈ clarkeJac f x,IsUnit V) :
    ∃ R C : ℝ,0 < R ∧ 0 < C ∧ ∀ y,‖y-x‖ < R → ∀ V ∈ clarkeJac f y,
      IsUnit V ∧ ∃ W : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n),
        W.comp V=ContinuousLinearMap.id ℝ _ ∧ ‖W‖ ≤ C := by
  obtain ⟨N,hN,C,hC⟩ := inverse_neighborhood f hf x hns
  obtain ⟨R,hR,hRN⟩ := Metric.mem_nhds_iff.mp hN
  refine ⟨R,max C 1,hR,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
  intro y hy V hV
  obtain ⟨W,hVW,hWV,hW⟩ := hC y (hRN (by simpa [Metric.mem_ball,dist_eq_norm] using hy)) V hV
  refine ⟨?_,W,hWV,hW.trans (le_max_left _ _)⟩
  exact ⟨⟨V,W,hVW,hWV⟩,rfl⟩

private theorem newton_step_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → E) (x y z : E) (V W : E →L[ℝ] E) (hroot : f x=0)
    (hWV : W.comp V=ContinuousLinearMap.id ℝ E) (hstep : V (z-y)=-f y)
    (C B : ℝ) (hC : 0 ≤ C) (hW : ‖W‖ ≤ C)
    (hres : ‖f y-f x-V (y-x)‖ ≤ B) : ‖z-x‖ ≤ C*B := by
  have hvz : V (z-x)=V (y-x)-f y := by
    have hid : z-x=(z-y)+(y-x) := by abel
    rw [hid,map_add,hstep]
    abel
  have hid : z-x=W (V (y-x)-f y) := by
    rw [← hvz,← ContinuousLinearMap.comp_apply,hWV,ContinuousLinearMap.id_apply]
  rw [hid]
  apply (W.le_opNorm _).trans
  apply mul_le_mul hW _ (norm_nonneg _) hC
  simpa [hroot,norm_sub_rev] using hres



private theorem local_contraction {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hf : LocallyLipschitz f)
    (x : EuclideanSpace ℝ (Fin n)) (hroot : f x=0) (hs : SemismoothAt f x)
    (hns : ∀ V ∈ clarkeJac f x,IsUnit V) :
    ∃ R C : ℝ,0 < R ∧ 0 < C ∧
      (∀ y,‖y-x‖ < R → ∀ V ∈ clarkeJac f y,IsUnit V ∧
        ∃ W : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n),
          W.comp V=ContinuousLinearMap.id ℝ _ ∧ ‖W‖ ≤ C) ∧
      (∀ y z,‖y-x‖ < R → ∀ V ∈ clarkeJac f y,V (z-y)=-f y → ‖z-x‖ ≤ ‖y-x‖/2) := by
  obtain ⟨r,C,hr,hC,hInv⟩ := inverse_ball f hf x hns
  obtain ⟨d,hd,hres⟩ := nonlinear_residual f hf x hs (1/(2*C)) (by positivity)
  refine ⟨min r d,C,lt_min hr hd,hC,?_,?_⟩
  · intro y hy V hV
    exact hInv y (hy.trans_le (min_le_left _ _)) V hV
  · intro y z hy V hV hstep
    obtain ⟨hunit,W,hWV,hW⟩ := hInv y (hy.trans_le (min_le_left _ _)) V hV
    have heq : x+(y-x)=y := by abel
    have hb : ‖f y-f x-V (y-x)‖ ≤ 1/(2*C)*‖y-x‖ := by
      simpa only [heq] using hres (y-x) (hy.trans_le (min_le_right _ _)) V (by simpa only [heq] using hV)
    have hs := newton_step_bound f x y z V W hroot hWV hstep C _ hC.le hW hb
    convert! hs using 1
    field_simp

private theorem run_geometric {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → E) (xstar : E) (R : ℝ) (hR : 0 < R)
    (hstep : ∀ y z,‖y-xstar‖ < R → ∀ V ∈ clarkeJac f y,
      V (z-y)=-f y → ‖z-xstar‖ ≤ ‖y-xstar‖/2)
    (x : ℕ → E) (V : ℕ → E →L[ℝ] E) (hzero : ‖x 0-xstar‖ < R) (hrun : IsNewtonRun f x V) :
    ∀ k,‖x k-xstar‖ < R ∧ ‖x k-xstar‖ ≤ (1/2 : ℝ)^k*‖x 0-xstar‖ := by
  intro k
  induction k with
  | zero => exact ⟨hzero,by simp⟩
  | succ k ih =>
    have hs := hstep (x k) (x (k+1)) ih.1 (V k) (hrun k).1 (hrun k).2
    constructor
    · nlinarith
    · calc
        ‖x (k+1)-xstar‖ ≤ ‖x k-xstar‖/2 := hs
        _ ≤ ((1/2 : ℝ)^k*‖x 0-xstar‖)/2 := by linarith [ih.2]
        _ = (1/2 : ℝ)^(k+1)*‖x 0-xstar‖ := by rw [pow_succ]; ring

theorem newton_superlinear {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hf : LocallyLipschitz f)
    (xstar : EuclideanSpace ℝ (Fin n)) (hroot : f xstar=0) (hs : SemismoothAt f xstar)
    (hns : ∀ V ∈ clarkeJac f xstar,IsUnit V) :
    ∃ δ > 0,
      (∀ y,‖y-xstar‖ < δ → ∀ W ∈ clarkeJac f y,IsUnit W) ∧
      (∀ y y',‖y-xstar‖ < δ → ∀ W ∈ clarkeJac f y,W (y'-y)=-f y → ‖y'-xstar‖ < δ) ∧
      (∀ (x : ℕ → EuclideanSpace ℝ (Fin n))
        (V : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)),
        ‖x 0-xstar‖ < δ → IsNewtonRun f x V →
          (∀ k,IsUnit (V k)) ∧ Tendsto x atTop (𝓝 xstar) ∧
          (fun k => x (k+1)-xstar) =o[atTop] (fun k => x k-xstar)) := by
  obtain ⟨R,C,hR,hC,hInv,hstep⟩ := local_contraction f hf xstar hroot hs hns
  refine ⟨R,hR,?_,?_,?_⟩
  · intro y hy V hV
    exact (hInv y hy V hV).1
  · intro y z hy V hV hVz
    have hb := hstep y z hy V hV hVz
    nlinarith
  · intro x V hx hrun
    have hgeo := run_geometric f xstar R hR hstep x V hx hrun
    have hpow : Tendsto (fun k : ℕ => (1/2 : ℝ)^k) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have hnconv : Tendsto (fun k => ‖x k-xstar‖) atTop (𝓝 0) := by
      apply squeeze_zero (fun k => norm_nonneg _) (fun k => (hgeo k).2)
      simpa using hpow.mul_const ‖x 0-xstar‖
    refine ⟨fun k => (hInv (x k) (hgeo k).1 (V k) (hrun k).1).1,
      tendsto_iff_norm_sub_tendsto_zero.mpr hnconv,?_⟩
    apply Asymptotics.IsLittleO.of_bound
    intro eps heps
    obtain ⟨d,hd,hres⟩ := nonlinear_residual f hf xstar hs (eps/C) (by positivity)
    filter_upwards [hnconv.eventually (eventually_lt_nhds hd)] with k hk
    obtain ⟨hunit,W,hWV,hW⟩ := hInv (x k) (hgeo k).1 (V k) (hrun k).1
    have heq : xstar+(x k-xstar)=x k := by abel
    have hb : ‖f (x k)-f xstar-(V k) (x k-xstar)‖ ≤ eps/C*‖x k-xstar‖ := by
      simpa only [heq] using hres (x k-xstar) hk (V k) (by simpa only [heq] using (hrun k).1)
    have hnext := newton_step_bound f xstar (x k) (x (k+1)) (V k) W hroot hWV (hrun k).2
      C _ hC.le hW hb
    convert! hnext using 1
    field_simp



theorem newton_order {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hf : LocallyLipschitz f)
    (xstar : EuclideanSpace ℝ (Fin n)) (hroot : f xstar=0) (hs : SemismoothAt f xstar)
    (hns : ∀ V ∈ clarkeJac f xstar,IsUnit V) (p : ℝ) (hp : 0 < p)
    (hord : POrderSemismoothAt p f xstar) :
    ∃ δ > 0,∃ C : ℝ,∀ (x : ℕ → EuclideanSpace ℝ (Fin n))
      (V : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)),
      ‖x 0-xstar‖ < δ → IsNewtonRun f x V →
        ∀ k,‖x (k+1)-xstar‖ ≤ C*‖x k-xstar‖^(1+p) := by
  obtain ⟨R,B,hR,hB,hInv,hstep⟩ := local_contraction f hf xstar hroot hs hns
  obtain ⟨C,r,hC,hr,hres⟩ := porder_nonlinear_residual f hf xstar p hp hord
  refine ⟨min R r,lt_min hR hr,B*C,?_⟩
  intro x V hx hrun k
  have hgeo := run_geometric f xstar (min R r) (lt_min hR hr)
    (fun y z hy W hW hw => hstep y z (hy.trans_le (min_le_left _ _)) W hW hw) x V hx hrun
  obtain ⟨hunit,W,hWV,hW⟩ := hInv (x k) ((hgeo k).1.trans_le (min_le_left _ _)) (V k) (hrun k).1
  have heq : xstar+(x k-xstar)=x k := by abel
  have hb : ‖f (x k)-f xstar-(V k) (x k-xstar)‖ ≤ C*‖x k-xstar‖^(1+p) := by
    simpa only [heq] using hres (x k-xstar) ((hgeo k).1.trans_le (min_le_right _ _))
      (V k) (by simpa only [heq] using (hrun k).1)
  have hh := newton_step_bound f xstar (x k) (x (k+1)) (V k) W hroot hWV (hrun k).2 B _ hB.le hW hb
  simpa only [mul_assoc] using hh

end NonsmoothHelpers

namespace NonsmoothNewton.Local

/-- Qi–Sun (1993), Theorem 3.2 (second sentence), p. 359. Under the hypotheses of Theorem 3.2,
if in addition `F` is `p`-order semismooth at `x*` (`0 < p ≤ 1`), the convergence of (3.2) is
of order `1 + p`: there are `δ > 0` and `C` such that every run started within `δ` of `x*`
satisfies `‖x^{k+1} - x*‖ ≤ C ‖x^k - x*‖^{1+p}` for all `k`. -/
theorem _root_.solution {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hF : LocallyLipschitz F)
    (xstar : EuclideanSpace ℝ (Fin n)) (hroot : F xstar = 0) (hsemi : SemismoothAt F xstar)
    (hns : ∀ V ∈ NonsmoothNewton.Shared.clarkeJac F xstar, IsUnit V)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (hpord : POrderSemismoothAt p F xstar) :
    ∃ δ > 0, ∃ C : ℝ, ∀ (x : ℕ → EuclideanSpace ℝ (Fin n))
      (V : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)),
      ‖x 0 - xstar‖ < δ → IsNewtonRun F x V →
        ∀ k, ‖x (k + 1) - xstar‖ ≤ C * ‖x k - xstar‖ ^ (1 + p) := by
  exact NonsmoothHelpers.newton_order F hF xstar hroot hsemi hns p hp0 hpord

end NonsmoothNewton.Local
