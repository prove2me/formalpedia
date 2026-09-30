-- Prove2me | solution 1 for NonsmoothNewton.Local.cor_2_5
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T11:16:48.508723+00:00
-- url     : https://prove2.me/submissions/e0ba5a72-7250-46e0-ae6f-722c7d42dd44

import Definitions.Def_NonsmoothNewton_Local_SemismoothAt
import Theorems.Thm_NonsmoothNewton_Shared_exists_local_clarkeJac_subset_thickening
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Tactic
open Filter Topology
open NonsmoothNewton.Shared NonsmoothNewton.Local

private theorem clarke_strict_singleton {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (F : E → G) (x : E) (F' : E →L[ℝ] G) (hstrong : HasStrictFDerivAt F F' x) :
    clarkeJac F x ⊆ {F'} := by
  have hb : bJac F x ⊆ {F'} := by
    intro V hV
    obtain ⟨u,hu,hdu,hVu⟩ := hV
    have hR : HasStrictFDerivAt (fun z => F z-F' z) (0 : E →L[ℝ] G) x := by
      convert! hstrong.sub (F'.hasStrictFDerivAt : HasStrictFDerivAt (fun z => F' z) F' x) using 1 <;> simp
    have hnorm : ‖V-F'‖ ≤ 0 := by
      apply le_of_forall_pos_le_add
      intro eps heps
      let epsN : NNReal := ⟨eps,heps.le⟩
      obtain ⟨U,hU,hLip⟩ := hR.exists_lipschitzOnWith_of_nnnorm_lt epsN (by rw [nnnorm_zero]; exact_mod_cast heps)
      have hevent : ∀ᶠ k in atTop, ‖fderiv ℝ F (u k)-F'‖ ≤ eps := by
        filter_upwards [hu.eventually (interior_mem_nhds.mpr hU)] with k hk
        exact ((hdu k).hasFDerivAt.sub F'.hasFDerivAt).le_of_lipschitzOn (mem_interior_iff_mem_nhds.mp hk) hLip
      have hh := le_of_tendsto ((hVu.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => F') atTop (𝓝 F'))).norm) hevent
      simpa only [zero_add] using hh
    have he : V=F' := sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg _)))
    exact he
  exact convexHull_min hb (convex_singleton F')

theorem solution {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    (F : E → G) (hF : LocallyLipschitz F) (x : E) (F' : E →L[ℝ] G)
    (hstrong : HasStrictFDerivAt F F' x) :
    SemismoothAt F x := by
  refine ⟨hstrong.exists_lipschitzOnWith,?_⟩
  intro h
  refine ⟨F' h,?_⟩
  intro eps heps
  let H := ‖h‖+1
  let K := ‖F'‖+1
  have hH : 0 < H := by dsimp [H]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  have heH : 0 < eps/(4*H) := by positivity
  obtain ⟨d,hd,hnear⟩ := exists_local_clarkeJac_subset_thickening F hF x heH
  let delta := min 1 (min (d/H) (eps/(4*K)))
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  refine ⟨delta,hdelta,?_⟩
  intro t h' ht0 htd hhd V hV
  have hd1 : delta ≤ 1 := min_le_left _ _
  have hdd : delta ≤ d/H := (min_le_right _ _).trans (min_le_left _ _)
  have hde : delta ≤ eps/(4*K) := (min_le_right _ _).trans (min_le_right _ _)
  have hh : ‖h'‖ ≤ H := by
    have hn := norm_le_norm_sub_add h' h
    dsimp [H]
    linarith
  have hdist : dist (x+t • h') x < d := by
    rw [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos ht0]
    have htt : t*H < d := (lt_div_iff₀ hH).mp (htd.trans_le hdd)
    exact (mul_le_mul_of_nonneg_left hh ht0.le).trans_lt htt
  have hthick := hnear (x+t • h') hdist hV
  obtain ⟨W,hW,hVW⟩ := Metric.mem_thickening_iff.mp hthick
  have heW : W=F' := clarke_strict_singleton F x F' hstrong hW
  rw [heW,dist_eq_norm] at hVW
  have h1 : ‖(V-F') h'‖ ≤ eps/4 := by
    apply ((V-F').le_opNorm h').trans
    have hm := mul_le_mul hVW.le hh (norm_nonneg h') heH.le
    have hid : eps/(4*H)*H=eps/4 := by field_simp
    exact hm.trans_eq hid
  have h2 : ‖F' (h'-h)‖ ≤ eps/4 := by
    apply (F'.le_opNorm (h'-h)).trans
    have hm := mul_le_mul (show ‖F'‖ ≤ K by dsimp [K]; linarith)
      (hhd.le.trans hde) (norm_nonneg _) hK.le
    have hid : K*(eps/(4*K))=eps/4 := by field_simp
    exact hm.trans_eq hid
  have hid : V h'-F' h = (V-F') h'+F' (h'-h) := by simp only [ContinuousLinearMap.sub_apply,map_sub]; abel
  rw [hid]
  exact (norm_add_le _ _).trans_lt (by linarith)



