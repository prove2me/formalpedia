-- Prove2me | solution 1 for NonsmoothNewton.Local.theorem_2_3
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T12:50:39.326831+00:00
-- url     : https://prove2.me/submissions/3dae6e88-ce32-4a37-8470-b4cbf13d5a4b

import Mathlib
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



theorem residual_implies_semi {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    (f : E → G) (hf : LocallyLipschitz f) (x : E)
    (hdir : ∀ h,∃ d,HasDirDerivAt f x h d)
    (hres : ∀ eps > 0,∃ δ > 0,∀ h : E,‖h‖ < δ → ∀ V ∈ clarkeJac f (x+h),
      ‖V h-dirDeriv f x h‖ ≤ eps*‖h‖) : SemismoothAt f x := by
  obtain ⟨K,hK⟩ := directional_lipschitz f hf x hdir
  refine ⟨hf x,?_⟩
  intro h
  refine ⟨dirDeriv f x h,?_⟩
  intro eps heps
  let H := ‖h‖+1
  let C := (K : ℝ)+1
  have hH : 0 < H := by dsimp [H]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨d,hd,hds⟩ := hres (eps/(4*H)) (by positivity)
  let δ := min 1 (min (d/H) (eps/(4*C)))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ,hδ,?_⟩
  intro t v ht htd hvd V hV
  have hv : ‖v‖ ≤ H := by
    have h := norm_le_norm_sub_add v h
    have hδ1 : δ ≤ 1 := min_le_left _ _
    dsimp [H]
    linarith
  have htdH : t*H < d := (lt_div_iff₀ hH).mp
    (htd.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  have hvsmall : ‖t • v‖ < d := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos ht]
    exact (mul_le_mul_of_nonneg_left hv ht.le).trans_lt htdH
  have hs := hds (t • v) hvsmall V hV
  rw [directional_smul f x v (hdir v) t ht.le,map_smul,← smul_sub,norm_smul,
    norm_smul,Real.norm_eq_abs,abs_of_pos ht] at hs
  have hscale : ‖V v-dirDeriv f x v‖ ≤ eps/(4*H)*‖v‖ := by nlinarith
  have hn : ‖V v-dirDeriv f x v‖ ≤ eps/4 := by
    apply hscale.trans
    calc
      eps/(4*H)*‖v‖ ≤ eps/(4*H)*H := mul_le_mul_of_nonneg_left hv (by positivity)
      _ = eps/4 := by field_simp
  have hvh : ‖dirDeriv f x v-dirDeriv f x h‖ ≤ eps/4 := by
    rw [← dist_eq_norm]
    apply (hK.dist_le_mul v h).trans
    rw [dist_eq_norm]
    calc
      (K : ℝ)*‖v-h‖ ≤ C*(eps/(4*C)) := mul_le_mul
        (by dsimp [C]; linarith)
        (hvd.le.trans ((min_le_right _ _).trans (min_le_right _ _))) (norm_nonneg _) hC.le
      _ = eps/4 := by field_simp
  have hid : V v-dirDeriv f x h=(V v-dirDeriv f x v)+(dirDeriv f x v-dirDeriv f x h) := by abel
  rw [hid]
  exact (norm_add_le _ _).trans_lt (by linarith)

theorem classical_residual_to_clarke {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    (f : E → G) (hf : LocallyLipschitz f) (x : E)
    (hdir : ∀ h,∃ d,HasDirDerivAt f x h d)
    (hres : ∀ eps > 0,∃ δ > 0,∀ h : E,‖h‖ < δ → DifferentiableAt ℝ f (x+h) →
      ‖fderiv ℝ f (x+h) h-dirDeriv f x h‖ ≤ eps*‖h‖) :
    ∀ eps > 0,∃ δ > 0,∀ h : E,‖h‖ < δ → ∀ V ∈ clarkeJac f (x+h),
      ‖V h-dirDeriv f x h‖ ≤ eps*‖h‖ := by
  obtain ⟨K,hK⟩ := directional_lipschitz f hf x hdir
  intro eps heps
  obtain ⟨δ,hδ,hds⟩ := hres eps heps
  refine ⟨δ,hδ,?_⟩
  intro h hh V hV
  have hb : ∀ W ∈ bJac f (x+h),‖W h-dirDeriv f x h‖ ≤ eps*‖h‖ := by
    intro W hW
    obtain ⟨u,hu,hdu,hVu⟩ := hW
    have hseq : Tendsto (fun k => u k-x) atTop (𝓝 h) := by
      simpa using hu.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => x) atTop (𝓝 x))
    have hevent : ∀ᶠ k in atTop,
        ‖fderiv ℝ f (u k) (u k-x)-dirDeriv f x (u k-x)‖ ≤ eps*‖u k-x‖ := by
      filter_upwards [hseq.norm.eventually (eventually_lt_nhds hh)] with k hk
      have heq : x+(u k-x)=u k := by abel
      simpa only [heq] using hds (u k-x) hk (by simpa only [heq] using hdu k)
    have hVu' : Tendsto (fun k => fderiv ℝ f (u k)) atTop (𝓝 W) := hVu
    have heval : Continuous (fun a : (E →L[ℝ] G) × E => a.1 a.2) :=
      continuous_fst.clm_apply continuous_snd
    have hact := (heval.tendsto (W,h)).comp (hVu'.prodMk_nhds hseq)
    have hleft := (hact.sub ((hK.continuous.tendsto h).comp hseq)).norm
    have hright := (tendsto_const_nhds : Tendsto (fun _ : ℕ => eps) atTop (𝓝 eps)).mul hseq.norm
    exact le_of_tendsto_of_tendsto hleft hright hevent
  have hc : Convex ℝ {W : E →L[ℝ] G | ‖W h-dirDeriv f x h‖ ≤ eps*‖h‖} := by
    convert! (convex_closedBall (dirDeriv f x h) (eps*‖h‖)).linear_preimage
      ((ContinuousLinearMap.apply ℝ G h).toLinearMap) using 1
    ext W
    simp [Metric.mem_closedBall,dist_eq_norm]
  exact convexHull_min hb hc hV

end NonsmoothHelpers

namespace NonsmoothNewton.Local

/-- Qi–Sun (1993), Theorem 2.3, p. 356, parts (i) ⇔ (iv) ⇔ (v). For locally Lipschitz `F`:
(i) `F` is semismooth at `x`;
(iv) `F'(x; ·)` exists and `V h - F'(x; h) = o(‖h‖)` for `V ∈ ∂F(x + h)`, `h → 0` (2.8);
(v) `F'(x; ·)` exists and `(F'(x + h; h) - F'(x; h)) / ‖h‖ → 0` as `h → 0` with
`x + h ∈ D_F` (2.9), where at a point of differentiability `F'(x + h; h) = JF(x + h) h`. -/
theorem _root_.solution {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    (F : E → G) (hF : LocallyLipschitz F) (x : E) :
    (SemismoothAt F x ↔
      ((∀ h : E, ∃ d : G, HasDirDerivAt F x h d) ∧
        ∀ ε > 0, ∃ δ > 0, ∀ h : E, ‖h‖ < δ → ∀ V ∈ NonsmoothNewton.Shared.clarkeJac F (x + h),
          ‖V h - dirDeriv F x h‖ ≤ ε * ‖h‖)) ∧
    (SemismoothAt F x ↔
      ((∀ h : E, ∃ d : G, HasDirDerivAt F x h d) ∧
        ∀ ε > 0, ∃ δ > 0, ∀ h : E, ‖h‖ < δ → DifferentiableAt ℝ F (x + h) →
          ‖fderiv ℝ F (x + h) h - dirDeriv F x h‖ ≤ ε * ‖h‖)) := by
  constructor
  · constructor
    · intro hs
      exact ⟨NonsmoothHelpers.semi_directional F hF x hs,NonsmoothHelpers.semi_uniform_residual F hF x hs⟩
    · rintro ⟨hd,hr⟩
      exact NonsmoothHelpers.residual_implies_semi F hF x hd hr
  · constructor
    · intro hs
      refine ⟨NonsmoothHelpers.semi_directional F hF x hs,?_⟩
      intro eps heps
      obtain ⟨δ,hδ,hd⟩ := NonsmoothHelpers.semi_uniform_residual F hF x hs eps heps
      refine ⟨δ,hδ,?_⟩
      intro h hh hdiff
      exact hd h hh _ (NonsmoothHelpers.fderiv_mem_clarke F (x+h) hdiff)
    · rintro ⟨hd,hr⟩
      exact NonsmoothHelpers.residual_implies_semi F hF x hd
        (NonsmoothHelpers.classical_residual_to_clarke F hF x hd hr)

end NonsmoothNewton.Local
