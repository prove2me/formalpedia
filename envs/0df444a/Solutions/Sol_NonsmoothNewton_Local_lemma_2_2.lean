-- Prove2me | solution 1 for NonsmoothNewton.Local.lemma_2_2
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T12:36:22.848316+00:00
-- url     : https://prove2.me/submissions/c12f10b9-4f3c-44c8-98b5-f04f349cd441

import Mathlib
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

end NonsmoothHelpers

namespace NonsmoothNewton.Local

/-- Qi–Sun (1993), Lemma 2.2, p. 356. If `F` is locally Lipschitz and `F'(x; h)` exists for
every `h`, then (i) `h ↦ F'(x; h)` is Lipschitz and (ii) for every `h` there is
`V ∈ ∂F(x)` with `F'(x; h) = V h`. -/
theorem _root_.solution {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    (F : E → G) (hF : LocallyLipschitz F) (x : E)
    (hdir : ∀ h : E, ∃ d : G, HasDirDerivAt F x h d) :
    (∃ K : NNReal, LipschitzWith K (fun h : E => dirDeriv F x h)) ∧
    ∀ h : E, ∃ V ∈ NonsmoothNewton.Shared.clarkeJac F x, dirDeriv F x h = V h := by
  refine ⟨NonsmoothHelpers.directional_lipschitz F hF x hdir,?_⟩
  intro h
  exact NonsmoothHelpers.directional_in_clarke F hF x h _
    (NonsmoothHelpers.directional_exists_value F x h (hdir h))

end NonsmoothNewton.Local
