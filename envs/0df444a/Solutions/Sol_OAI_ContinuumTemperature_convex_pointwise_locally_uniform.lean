-- Prove2me | solution 1 for OAI.ContinuumTemperature.convex_pointwise_locally_uniform
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T19:04:35.278264+00:00
-- url     : https://prove2.me/submissions/884c95f0-202d-4c61-a8ca-ab4fb3e1248e

import Mathlib

section
-- module Solutions.OAIQW_ContinuumTemperature.ConvexUniform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2

section
open scoped Topology NNReal
open Filter Set Metric
noncomputable section
namespace ContinuumTemperature

variable {E : Type u_1} {ι : Type u_2} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {l : Filter ι} [l.NeBot] {S : Set E} {F : ι → E → ℝ} {f : E → ℝ}

omit [FiniteDimensional ℝ E] in
lemma convexOn_of_pointwise_tendsto (hconv : ∀ᶠ i in l, ConvexOn ℝ S (F i))
    (hlim : ∀ x ∈ S, Tendsto (fun i => F i x) l (𝓝 (f x))) : ConvexOn ℝ S f := by
  obtain ⟨i,hi⟩ := hconv.exists
  refine ⟨hi.1,?_⟩
  intro x hx y hy a b ha hb hab
  have hz := hi.1 hx hy ha hb hab
  exact le_of_tendsto_of_tendsto (hlim _ hz)
    (((hlim x hx).const_mul a).add ((hlim y hy).const_mul b))
    (hconv.mono fun i hi => hi.2 hx hy ha hb hab)

omit [l.NeBot] in

lemma eventually_convex_lipschitz (hS : IsOpen S)
    (hconv : ∀ᶠ i in l, ConvexOn ℝ S (F i))
    (hlim : ∀ x ∈ S, Tendsto (fun i => F i x) l (𝓝 (f x))) {x : E} (hx : x ∈ S) :
    ∃ r > 0, ball x r ⊆ S ∧ ∃ C : ℝ≥0, ∀ᶠ i in l, LipschitzOnWith C (F i) (ball x r) := by
  obtain ⟨b,hxb,hbS⟩ := exists_mem_interior_convexHull_affineBasis (hS.mem_nhds hx)
  obtain ⟨M,hM⟩ := (finite_range (fun j => f (b j))).bddAbove
  let C : ℝ := |M|+|f x|+2
  have hC : 0 < C := by dsimp [C]; positivity
  have hv : ∀ᶠ i in l, ∀ j, F i (b j) ≤ C := by
    apply eventually_all.mpr
    intro j
    have hb : b j ∈ S := hbS (subset_convexHull ℝ _ (mem_range_self j))
    filter_upwards [(hlim _ hb).eventually_lt_const (show f (b j) < f (b j)+1 by linarith)] with i hi
    have hm := hM (mem_range_self j)
    have hMle := le_abs_self M
    have hxf := abs_nonneg (f x)
    dsimp [C]
    linarith
  have hxlower : ∀ᶠ i in l, -C ≤ F i x := by
    filter_upwards [(hlim _ hx).eventually_const_lt (show f x-1 < f x by linarith)] with i hi
    have hxabs := neg_abs_le (f x)
    have hm := abs_nonneg M
    dsimp [C]
    linarith
  obtain ⟨r,hr,hrb⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hxb)
  have hrh : ball x r ⊆ convexHull ℝ (range b) := hrb.trans interior_subset
  refine ⟨r/2,by positivity,(ball_subset_ball (by linarith : r/2 ≤ r)).trans (hrh.trans hbS),
    (2*(3*C)/(r/2)).toNNReal,?_⟩
  filter_upwards [hconv,hv,hxlower] with i hi hiv hix
  have hub : ∀ y ∈ convexHull ℝ (range b), F i y ≤ C := by
    have hh : convexHull ℝ (range b) ⊆ {y ∈ S | F i y ≤ C} :=
      convexHull_min (by rintro y ⟨j,rfl⟩; exact ⟨hbS (subset_convexHull ℝ _ (mem_range_self j)),hiv j⟩)
        (hi.convex_le C)
    exact fun y hy => (hh hy).2
  have habs : ∀ y, dist y x < r → |F i y| ≤ 3*C := by
    intro y hy
    have hyb := hrh hy
    have hreflect : 2 • x-y ∈ ball x r := by
      rw [mem_ball,dist_eq_norm_sub,show 2 • x-y-x = x-y by module,norm_sub_rev]
      simpa only [dist_eq_norm_sub] using hy
    have huby := hub y hyb
    have hubr := hub _ (hrh hreflect)
    have hmid := hi.2 (hbS hyb) (hbS (hrh hreflect))
      (show (0:ℝ) ≤ 1/2 by norm_num) (show (0:ℝ) ≤ 1/2 by norm_num)
      (show (1/2:ℝ)+1/2=1 by norm_num)
    have he : (1/2:ℝ) • y + (1/2:ℝ) • (2 • x-y) = x := by module
    rw [he] at hmid
    simp only [smul_eq_mul] at hmid
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hL := (hi.subset (hrh.trans hbS) (convex_ball x r)).lipschitzOnWith_of_abs_le
    (show 0 < r/2 by positivity) habs
  simpa only [show r-r/2=r/2 by ring] using hL

theorem convex_pointwise_locally_uniform_oai (hS : IsOpen S)
    (hconv : ∀ᶠ i in l, ConvexOn ℝ S (F i))
    (hlim : ∀ x ∈ S, Tendsto (fun i => F i x) l (𝓝 (f x))) :
    TendstoLocallyUniformlyOn F f l S := by
  have hf := (convexOn_of_pointwise_tendsto hconv hlim).continuousOn hS
  apply Metric.tendstoLocallyUniformlyOn_iff.mpr
  intro ε hε x hx
  obtain ⟨r,hr,_,C,hC⟩ := eventually_convex_lipschitz hS hconv hlim hx
  have hfnear : ∀ᶠ y in 𝓝 x, dist (f y) (f x) < ε/3 :=
    (hf.continuousAt (hS.mem_nhds hx)).eventually (ball_mem_nhds _ (by positivity))
  let T := ball x r ∩ ball x (ε/(3*((C:ℝ)+1))) ∩ {y | dist (f y) (f x) < ε/3}
  have hT : T ∈ 𝓝 x := inter_mem (inter_mem (ball_mem_nhds _ hr)
    (ball_mem_nhds _ (by positivity))) hfnear
  refine ⟨T,nhdsWithin_le_nhds hT,?_⟩
  filter_upwards [hC,(hlim x hx).eventually (ball_mem_nhds _ (show 0 < ε/3 by positivity))]
    with i hi hxlim
  intro y hy
  have hd := lipschitzOnWith_iff_dist_le_mul.mp hi x (mem_ball_self hr) y hy.1.1
  have hεC : 0 < 3*((C:ℝ)+1) := by positivity
  have hyd : dist x y < ε/(3*((C:ℝ)+1)) := by simpa only [mem_ball,dist_comm] using hy.1.2
  have hdd : (C:ℝ)*dist x y < ε/3 := by
    have he := (lt_div_iff₀ hεC).mp hyd
    have hnn := dist_nonneg (x := x) (y := y)
    nlinarith
  have hb : dist (f x) (F i x) < ε/3 := by simpa only [mem_ball,dist_comm] using hxlim
  have hyf : dist (f y) (f x) < ε/3 := hy.2
  calc
    dist (f y) (F i y) ≤ dist (f y) (f x)+dist (f x) (F i x)+dist (F i x) (F i y) := dist_triangle4 _ _ _ _
    _ < ε := by linarith only [hyf,hb,hd,hdd]

end ContinuumTemperature
end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.ContinuumTemperature.convex_pointwise_locally_uniform_oai.{u_1, u_2} := @OAI.ContinuumTemperature.convex_pointwise_locally_uniform_oai.{u_1, u_2}
