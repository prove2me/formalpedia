-- Prove2me | solution 1 for OAI.CubicTorus.fourCorner_normalized_contradiction
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T17:23:24.48319+00:00
-- url     : https://prove2.me/submissions/60dcdd3c-444c-4389-af68-868a3dbf518a

import Mathlib
import Definitions.Def_OAIQ079A000
import Theorems.Thm_OAI_CubicTorus_corner_grid_202
import Theorems.Thm_OAI_CubicTorus_corner_grid_269
import Theorems.Thm_OAI_CubicTorus_corner_grid_332

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_FourStarScalarGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace CubicTorus

lemma corner_root_d_bound {t d x : ℝ} (ht0 : 0≤t) (ht : t<1) (hx : 0≤x)
    (he : Real.pi*(1-t-d^2)=x*(1-t^2)) : d^2≤1-t := by
  have ha : 0≤1-t^2 := by nlinarith
  have hh : 0≤Real.pi*(1-t-d^2) := he ▸ mul_nonneg hx ha
  have := (mul_nonneg_iff_of_pos_left Real.pi_pos).mp hh
  linarith

lemma corner_root_interval_bound {t d x l u D X : ℝ}
    (ht0 : 0≤t) (hd0 : 0≤d) (hx0 : 0≤x)
    (he : Real.pi*(1-t-d^2)=x*(1-t^2))
    (hl : l≤t) (hu : t≤u) (hD : D≤d) (hD0 : 0≤D)
    (hu1 : u<1) (hc : 0≤1-l-D^2)
    (hnum : (22/7 : ℝ)*(1-l-D^2)≤X*(1-u^2)) : x≤X := by
  have hpu : Real.pi≤(22/7 : ℝ) := by linarith [Real.pi_lt_d4]
  have hds : D^2≤d^2 := by nlinarith
  have hts : t^2≤u^2 := by nlinarith
  have ha := mul_nonneg hx0 (sub_nonneg.mpr hts)
  have hb := mul_nonneg Real.pi_pos.le (show 0≤t-l+(d^2-D^2) by linarith)
  have hp := mul_le_mul_of_nonneg_right hpu hc
  have hq : x*(1-u^2)≤X*(1-u^2) := by nlinarith only [he,ha,hb,hp,hnum]
  exact (mul_le_mul_iff_left₀ (show 0<1-u^2 by nlinarith)).mp hq

lemma corner_box_strict {t d x u E X : ℝ}
    (ht0 : 0≤t) (hd0 : 0≤d) (hx0 : 0≤x)
    (hu : t≤u) (hE : d≤E) (hX : x≤X)
    (hnum : E+(u^2+(u+X*E)^2)/(157/50 : ℝ)<1) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hu0 : 0≤u := ht0.trans hu
  have hE0 : 0≤E := hd0.trans hE
  have hX0 : 0≤X := hx0.trans hX
  have hm := mul_le_mul hX hE hd0 hX0
  have hsum : t+x*d≤u+X*E := by linarith
  have hsum0 : 0≤t+x*d := add_nonneg ht0 (mul_nonneg hx0 hd0)
  have hs : t^2+(t+x*d)^2≤u^2+(u+X*E)^2 := by nlinarith
  have hp : (157/50 : ℝ)<Real.pi := by linarith [Real.pi_gt_d4]
  have hs0 : 0≤u^2+(u+X*E)^2 := by positivity
  have hdiv := div_le_div_of_nonneg_left hs0 (by norm_num : (0 : ℝ)<157/50) hp.le
  have hdiv' := div_le_div_of_nonneg_right hs Real.pi_pos.le
  linarith

end CubicTorus

end
end

section

noncomputable section
namespace CubicTorus

namespace CornerRootData
lemma dbound {t d x : ℝ} (h : CornerRootData t d x) : d^2≤1-t :=
  corner_root_d_bound h.t0 h.t1 h.x0 h.root
end CornerRootData

end CubicTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_CornerGrid269
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace CubicTorus

private lemma corner_grid_333 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/2 : ℝ)≤t) (hu : t≤(17/32 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(169/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(1582592/1157625 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_334 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (17/32 : ℝ)≤t) (hu : t≤(9/16 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(65/144 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(50864/39375 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_335 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (17/32 : ℝ)≤t) (hu : t≤(9/16 : ℝ))
    (hd : (65/144 : ℝ)≤d) (he : d≤(169/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(3454/2835 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_336 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (17/32 : ℝ)≤t) (hu : t≤(9/16 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(169/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (65/144 : ℝ) with hm|hm
  · exact corner_grid_334 h hl hu hd hm
  · exact corner_grid_335 h hl hu hm.le he

private lemma corner_grid_337 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/2 : ℝ)≤t) (hu : t≤(9/16 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(169/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (17/32 : ℝ) with hm|hm
  · exact corner_grid_333 h hl hm hd he
  · exact corner_grid_336 h hm.le hu hd he

private lemma corner_grid_338 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/2 : ℝ)≤t) (hu : t≤(17/32 : ℝ))
    (hd : (169/360 : ℝ)≤d) (he : d≤(39/80 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(1822304/1488375 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_339 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/2 : ℝ)≤t) (hu : t≤(17/32 : ℝ))
    (hd : (39/80 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(147752/128625 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_340 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/2 : ℝ)≤t) (hu : t≤(17/32 : ℝ))
    (hd : (169/360 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (39/80 : ℝ) with hm|hm
  · exact corner_grid_338 h hl hu hd hm
  · exact corner_grid_339 h hl hu hm.le he

private lemma corner_grid_341 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (17/32 : ℝ)≤t) (hu : t≤(9/16 : ℝ))
    (hd : (169/360 : ℝ)≤d) (he : d≤(39/80 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(2832632/2480625 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_342 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (17/32 : ℝ)≤t) (hu : t≤(9/16 : ℝ))
    (hd : (39/80 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(32538/30625 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_343 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (17/32 : ℝ)≤t) (hu : t≤(9/16 : ℝ))
    (hd : (169/360 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (39/80 : ℝ) with hm|hm
  · exact corner_grid_341 h hl hu hd hm
  · exact corner_grid_342 h hl hu hm.le he

private lemma corner_grid_344 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/2 : ℝ)≤t) (hu : t≤(9/16 : ℝ))
    (hd : (169/360 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (17/32 : ℝ) with hm|hm
  · exact corner_grid_340 h hl hm hd he
  · exact corner_grid_343 h hm.le hu hd he

private lemma corner_grid_345 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/2 : ℝ)≤t) (hu : t≤(9/16 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (169/360 : ℝ) with hm|hm
  · exact corner_grid_337 h hl hu hd hm
  · exact corner_grid_344 h hl hu hm.le he

private lemma corner_grid_346 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/16 : ℝ)≤t) (hu : t≤(19/32 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(65/144 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(1265792/1044225 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_347 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/16 : ℝ)≤t) (hu : t≤(19/32 : ℝ))
    (hd : (65/144 : ℝ)≤d) (he : d≤(169/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(426536/375921 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_348 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/16 : ℝ)≤t) (hu : t≤(19/32 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(169/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (65/144 : ℝ) with hm|hm
  · exact corner_grid_346 h hl hu hd hm
  · exact corner_grid_347 h hl hu hm.le he

private lemma corner_grid_349 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (19/32 : ℝ)≤t) (hu : t≤(5/8 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(65/144 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(5324/4725 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_350 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (19/32 : ℝ)≤t) (hu : t≤(5/8 : ℝ))
    (hd : (65/144 : ℝ)≤d) (he : d≤(169/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(3553/3402 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_351 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (19/32 : ℝ)≤t) (hu : t≤(5/8 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(169/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (65/144 : ℝ) with hm|hm
  · exact corner_grid_349 h hl hu hd hm
  · exact corner_grid_350 h hl hu hm.le he

private lemma corner_grid_352 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/16 : ℝ)≤t) (hu : t≤(5/8 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(169/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (19/32 : ℝ) with hm|hm
  · exact corner_grid_348 h hl hm hd he
  · exact corner_grid_351 h hm.le hu hd he

private lemma corner_grid_353 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/16 : ℝ)≤t) (hu : t≤(19/32 : ℝ))
    (hd : (169/360 : ℝ)≤d) (he : d≤(39/80 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(9904928/9398025 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_354 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/16 : ℝ)≤t) (hu : t≤(19/32 : ℝ))
    (hd : (39/80 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(112552/116025 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_355 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/16 : ℝ)≤t) (hu : t≤(19/32 : ℝ))
    (hd : (169/360 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (39/80 : ℝ) with hm|hm
  · exact corner_grid_353 h hl hu hd hm
  · exact corner_grid_354 h hl hu hm.le he

private lemma corner_grid_356 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (19/32 : ℝ)≤t) (hu : t≤(5/8 : ℝ))
    (hd : (169/360 : ℝ)≤d) (he : d≤(39/80 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(40766/42525 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_357 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (19/32 : ℝ)≤t) (hu : t≤(5/8 : ℝ))
    (hd : (39/80 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(913/1050 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_358 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (19/32 : ℝ)≤t) (hu : t≤(5/8 : ℝ))
    (hd : (169/360 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (39/80 : ℝ) with hm|hm
  · exact corner_grid_356 h hl hu hd hm
  · exact corner_grid_357 h hl hu hm.le he

private lemma corner_grid_359 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/16 : ℝ)≤t) (hu : t≤(5/8 : ℝ))
    (hd : (169/360 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (19/32 : ℝ) with hm|hm
  · exact corner_grid_355 h hl hm hd he
  · exact corner_grid_358 h hm.le hu hd he

private lemma corner_grid_360 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/16 : ℝ)≤t) (hu : t≤(5/8 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (169/360 : ℝ) with hm|hm
  · exact corner_grid_352 h hl hu hd hm
  · exact corner_grid_359 h hl hu hm.le he

lemma corner_grid_361 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/2 : ℝ)≤t) (hu : t≤(5/8 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (9/16 : ℝ) with hm|hm
  · exact corner_grid_345 h hl hm hd he
  · exact corner_grid_360 h hm.le hu hd he

private lemma corner_grid_362 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/2 : ℝ)≤t) (hu : t≤(17/32 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(377/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(11149952/10418625 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_363 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/2 : ℝ)≤t) (hu : t≤(17/32 : ℝ))
    (hd : (377/720 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(10302248/10418625 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_364 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/2 : ℝ)≤t) (hu : t≤(17/32 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (377/720 : ℝ) with hm|hm
  · exact corner_grid_362 h hl hu hd hm
  · exact corner_grid_363 h hl hu hm.le he

private lemma corner_grid_365 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (17/32 : ℝ)≤t) (hu : t≤(9/16 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(377/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(2431088/2480625 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_366 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (17/32 : ℝ)≤t) (hu : t≤(9/16 : ℝ))
    (hd : (377/720 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(2219162/2480625 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_367 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (17/32 : ℝ)≤t) (hu : t≤(9/16 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (377/720 : ℝ) with hm|hm
  · exact corner_grid_365 h hl hu hd hm
  · exact corner_grid_366 h hl hu hm.le he

private lemma corner_grid_368 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/2 : ℝ)≤t) (hu : t≤(9/16 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (17/32 : ℝ) with hm|hm
  · exact corner_grid_364 h hl hm hd he
  · exact corner_grid_367 h hm.le hu hd he

private lemma corner_grid_369 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/2 : ℝ)≤t) (hu : t≤(17/32 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(403/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(5984/6615 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_370 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/2 : ℝ)≤t) (hu : t≤(17/32 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(8517608/10418625 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_371 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/2 : ℝ)≤t) (hu : t≤(17/32 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (403/720 : ℝ) with hm|hm
  · exact corner_grid_369 h hl hu hd hm
  · exact corner_grid_370 h hl hu hm.le he

private lemma corner_grid_372 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (17/32 : ℝ)≤t) (hu : t≤(9/16 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(403/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(8888/11025 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_373 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (17/32 : ℝ)≤t) (hu : t≤(9/16 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(253286/354375 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_374 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (17/32 : ℝ)≤t) (hu : t≤(9/16 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (403/720 : ℝ) with hm|hm
  · exact corner_grid_372 h hl hu hd hm
  · exact corner_grid_373 h hl hu hm.le he

private lemma corner_grid_375 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/2 : ℝ)≤t) (hu : t≤(9/16 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (17/32 : ℝ) with hm|hm
  · exact corner_grid_371 h hl hm hd he
  · exact corner_grid_374 h hm.le hu hd he

lemma corner_grid_376 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/2 : ℝ)≤t) (hu : t≤(9/16 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (13/24 : ℝ) with hm|hm
  · exact corner_grid_368 h hl hu hd hm
  · exact corner_grid_375 h hl hu hm.le he

private lemma corner_grid_377 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/16 : ℝ)≤t) (hu : t≤(19/32 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(377/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(1185536/1342575 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_378 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/16 : ℝ)≤t) (hu : t≤(19/32 : ℝ))
    (hd : (377/720 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(7451048/9398025 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

lemma corner_grid_379 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/16 : ℝ)≤t) (hu : t≤(19/32 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (377/720 : ℝ) with hm|hm
  · exact corner_grid_377 h hl hu hd hm
  · exact corner_grid_378 h hl hu hm.le he

lemma corner_grid_380 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (19/32 : ℝ)≤t) (hu : t≤(5/8 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(377/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(33044/42525 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

end CubicTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_CornerGrid381
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace CubicTorus

private lemma corner_grid_381 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (19/32 : ℝ)≤t) (hu : t≤(5/8 : ℝ))
    (hd : (377/720 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(57937/85050 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_382 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (19/32 : ℝ)≤t) (hu : t≤(5/8 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (377/720 : ℝ) with hm|hm
  · exact corner_grid_380 h hl hu hd hm
  · exact corner_grid_381 h hl hu hm.le he

private lemma corner_grid_383 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/16 : ℝ)≤t) (hu : t≤(5/8 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (19/32 : ℝ) with hm|hm
  · exact corner_grid_379 h hl hm hd he
  · exact corner_grid_382 h hm.le hu hd he

private lemma corner_grid_384 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/16 : ℝ)≤t) (hu : t≤(19/32 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(403/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(29216/41769 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_385 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/16 : ℝ)≤t) (hu : t≤(19/32 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(5666408/9398025 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_386 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/16 : ℝ)≤t) (hu : t≤(19/32 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (403/720 : ℝ) with hm|hm
  · exact corner_grid_384 h hl hu hd hm
  · exact corner_grid_385 h hl hu hm.le he

private lemma corner_grid_387 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (19/32 : ℝ)≤t) (hu : t≤(5/8 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(110/189 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_388 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/16 : ℝ)≤t) (hu : t≤(5/8 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (19/32 : ℝ) with hm|hm
  · exact corner_grid_386 h hl hm hd he
  · exact corner_grid_387 h hm.le hu hd he

private lemma corner_grid_389 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/16 : ℝ)≤t) (hu : t≤(5/8 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (13/24 : ℝ) with hm|hm
  · exact corner_grid_383 h hl hu hd hm
  · exact corner_grid_388 h hl hu hm.le he

private lemma corner_grid_390 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/2 : ℝ)≤t) (hu : t≤(5/8 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (9/16 : ℝ) with hm|hm
  · exact corner_grid_376 h hl hm hd he
  · exact corner_grid_389 h hm.le hu hd he

private lemma corner_grid_391 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/2 : ℝ)≤t) (hu : t≤(5/8 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (91/180 : ℝ) with hm|hm
  · exact corner_grid_361 h hl hu hd hm
  · exact corner_grid_390 h hl hu hm.le he

private lemma corner_grid_392 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/8 : ℝ)≤t) (hu : t≤(21/32 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(65/144 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(86272/83475 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_393 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/8 : ℝ)≤t) (hu : t≤(21/32 : ℝ))
    (hd : (65/144 : ℝ)≤d) (he : d≤(169/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(536/567 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_394 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/8 : ℝ)≤t) (hu : t≤(21/32 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(169/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (65/144 : ℝ) with hm|hm
  · exact corner_grid_392 h hl hu hd hm
  · exact corner_grid_393 h hl hu hm.le he

private lemma corner_grid_395 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (21/32 : ℝ)≤t) (hu : t≤(11/16 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(65/144 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(197648/212625 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_396 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (21/32 : ℝ)≤t) (hu : t≤(11/16 : ℝ))
    (hd : (65/144 : ℝ)≤d) (he : d≤(169/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(63866/76545 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_397 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (21/32 : ℝ)≤t) (hu : t≤(11/16 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(169/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (65/144 : ℝ) with hm|hm
  · exact corner_grid_395 h hl hu hd hm
  · exact corner_grid_396 h hl hu hm.le he

private lemma corner_grid_398 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/8 : ℝ)≤t) (hu : t≤(11/16 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(169/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (21/32 : ℝ) with hm|hm
  · exact corner_grid_394 h hl hm hd he
  · exact corner_grid_397 h hm.le hu hd he

private lemma corner_grid_399 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/8 : ℝ)≤t) (hu : t≤(21/32 : ℝ))
    (hd : (169/360 : ℝ)≤d) (he : d≤(39/80 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(641248/751275 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_400 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/8 : ℝ)≤t) (hu : t≤(21/32 : ℝ))
    (hd : (39/80 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(7032/9275 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_401 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/8 : ℝ)≤t) (hu : t≤(21/32 : ℝ))
    (hd : (169/360 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (39/80 : ℝ) with hm|hm
  · exact corner_grid_399 h hl hu hd hm
  · exact corner_grid_400 h hl hu hm.le he

private lemma corner_grid_402 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (21/32 : ℝ)≤t) (hu : t≤(11/16 : ℝ))
    (hd : (169/360 : ℝ)≤d) (he : d≤(39/80 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(1407032/1913625 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_403 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (21/32 : ℝ)≤t) (hu : t≤(11/16 : ℝ))
    (hd : (39/80 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(2134/3375 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_404 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (21/32 : ℝ)≤t) (hu : t≤(11/16 : ℝ))
    (hd : (169/360 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (39/80 : ℝ) with hm|hm
  · exact corner_grid_402 h hl hu hd hm
  · exact corner_grid_403 h hl hu hm.le he

private lemma corner_grid_405 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/8 : ℝ)≤t) (hu : t≤(11/16 : ℝ))
    (hd : (169/360 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (21/32 : ℝ) with hm|hm
  · exact corner_grid_401 h hl hm hd he
  · exact corner_grid_404 h hm.le hu hd he

private lemma corner_grid_406 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/8 : ℝ)≤t) (hu : t≤(11/16 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (169/360 : ℝ) with hm|hm
  · exact corner_grid_398 h hl hu hd hm
  · exact corner_grid_405 h hl hu hm.le he

private lemma corner_grid_407 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/16 : ℝ)≤t) (hu : t≤(23/32 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(65/144 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(57472/70875 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_408 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/16 : ℝ)≤t) (hu : t≤(23/32 : ℝ))
    (hd : (65/144 : ℝ)≤d) (he : d≤(169/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(3608/5103 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_409 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/16 : ℝ)≤t) (hu : t≤(23/32 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(169/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (65/144 : ℝ) with hm|hm
  · exact corner_grid_407 h hl hu hd hm
  · exact corner_grid_408 h hl hu hm.le he

private lemma corner_grid_410 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (23/32 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(65/144 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(7403/11025 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_411 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (23/32 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (65/144 : ℝ)≤d) (he : d≤(169/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(17677/31752 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_412 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (23/32 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(169/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (65/144 : ℝ) with hm|hm
  · exact corner_grid_410 h hl hu hd hm
  · exact corner_grid_411 h hl hu hm.le he

private lemma corner_grid_413 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/16 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(169/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (23/32 : ℝ) with hm|hm
  · exact corner_grid_409 h hl hm hd he
  · exact corner_grid_412 h hm.le hu hd he

private lemma corner_grid_414 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/16 : ℝ)≤t) (hu : t≤(23/32 : ℝ))
    (hd : (169/360 : ℝ)≤d) (he : d≤(39/80 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(382048/637875 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_415 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/16 : ℝ)≤t) (hu : t≤(23/32 : ℝ))
    (hd : (39/80 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(3832/7875 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_416 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/16 : ℝ)≤t) (hu : t≤(23/32 : ℝ))
    (hd : (169/360 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (39/80 : ℝ) with hm|hm
  · exact corner_grid_414 h hl hu hd hm
  · exact corner_grid_415 h hl hu hm.le he

private lemma corner_grid_417 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (23/32 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (169/360 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(1771/4050 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_418 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/16 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (169/360 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (23/32 : ℝ) with hm|hm
  · exact corner_grid_416 h hl hm hd he
  · exact corner_grid_417 h hm.le hu hd he

private lemma corner_grid_419 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/16 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (169/360 : ℝ) with hm|hm
  · exact corner_grid_413 h hl hu hd hm
  · exact corner_grid_418 h hl hu hm.le he

private lemma corner_grid_420 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/8 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (11/16 : ℝ) with hm|hm
  · exact corner_grid_406 h hl hm hd he
  · exact corner_grid_419 h hm.le hu hd he

private lemma corner_grid_421 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/8 : ℝ)≤t) (hu : t≤(21/32 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(377/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(9344/14175 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_422 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/8 : ℝ)≤t) (hu : t≤(21/32 : ℝ))
    (hd : (377/720 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(418168/751275 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_423 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/8 : ℝ)≤t) (hu : t≤(21/32 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (377/720 : ℝ) with hm|hm
  · exact corner_grid_421 h hl hu hd hm
  · exact corner_grid_422 h hl hu hm.le he

private lemma corner_grid_424 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (21/32 : ℝ)≤t) (hu : t≤(11/16 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(1005488/1913625 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_425 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/8 : ℝ)≤t) (hu : t≤(11/16 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (21/32 : ℝ) with hm|hm
  · exact corner_grid_423 h hl hm hd he
  · exact corner_grid_424 h hm.le hu hd he

private lemma corner_grid_426 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/8 : ℝ)≤t) (hu : t≤(21/32 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(1504/3339 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_427 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (21/32 : ℝ)≤t) (hu : t≤(11/16 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(2552/8505 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_428 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/8 : ℝ)≤t) (hu : t≤(11/16 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (21/32 : ℝ) with hm|hm
  · exact corner_grid_426 h hl hm hd he
  · exact corner_grid_427 h hm.le hu hd he

private lemma corner_grid_429 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/8 : ℝ)≤t) (hu : t≤(11/16 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (13/24 : ℝ) with hm|hm
  · exact corner_grid_425 h hl hu hd hm
  · exact corner_grid_428 h hl hu hm.le he

private lemma corner_grid_430 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/16 : ℝ)≤t) (hu : t≤(23/32 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(236032/637875 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_431 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (23/32 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(18293/99225 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_432 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/16 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (23/32 : ℝ) with hm|hm
  · exact corner_grid_430 h hl hm hd he
  · exact corner_grid_431 h hm.le hu hd he

private lemma corner_grid_433 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/16 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(121/882 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_434 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/16 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (13/24 : ℝ) with hm|hm
  · exact corner_grid_432 h hl hu hd hm
  · exact corner_grid_433 h hl hu hm.le he

private lemma corner_grid_435 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/8 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (11/16 : ℝ) with hm|hm
  · exact corner_grid_429 h hl hm hd he
  · exact corner_grid_434 h hm.le hu hd he

private lemma corner_grid_436 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/8 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (91/180 : ℝ) with hm|hm
  · exact corner_grid_420 h hl hu hd hm
  · exact corner_grid_435 h hl hu hm.le he

private lemma corner_grid_437 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/2 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (5/8 : ℝ) with hm|hm
  · exact corner_grid_391 h hl hm hd he
  · exact corner_grid_436 h hm.le hu hd he

private lemma corner_grid_438 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/2 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (13/30 : ℝ) with hm|hm
  · exact corner_grid_332 h hl hu hd hm
  · exact corner_grid_437 h hl hu hm.le he

private lemma corner_grid_439 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/4 : ℝ)≤t) (hu : t≤(25/32 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(13/40 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(399872/297675 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_440 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (25/32 : ℝ)≤t) (hu : t≤(13/16 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(221/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(1542992/1233225 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_441 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (25/32 : ℝ)≤t) (hu : t≤(13/16 : ℝ))
    (hd : (221/720 : ℝ)≤d) (he : d≤(13/40 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(1420298/1233225 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_442 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (25/32 : ℝ)≤t) (hu : t≤(13/16 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(13/40 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (221/720 : ℝ) with hm|hm
  · exact corner_grid_440 h hl hu hd hm
  · exact corner_grid_441 h hl hu hm.le he

private lemma corner_grid_443 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/4 : ℝ)≤t) (hu : t≤(13/16 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(13/40 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (25/32 : ℝ) with hm|hm
  · exact corner_grid_439 h hl hm hd he
  · exact corner_grid_442 h hm.le hu hd he

private lemma corner_grid_444 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/4 : ℝ)≤t) (hu : t≤(25/32 : ℝ))
    (hd : (13/40 : ℝ)≤d) (he : d≤(247/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(3872/3325 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_445 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/4 : ℝ)≤t) (hu : t≤(25/32 : ℝ))
    (hd : (247/720 : ℝ)≤d) (he : d≤(13/36 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(6036008/5655825 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_446 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/4 : ℝ)≤t) (hu : t≤(25/32 : ℝ))
    (hd : (13/40 : ℝ)≤d) (he : d≤(13/36 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (247/720 : ℝ) with hm|hm
  · exact corner_grid_444 h hl hu hd hm
  · exact corner_grid_445 h hl hu hm.le he

private lemma corner_grid_447 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (25/32 : ℝ)≤t) (hu : t≤(13/16 : ℝ))
    (hd : (13/40 : ℝ)≤d) (he : d≤(247/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(15928/15225 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_448 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (25/32 : ℝ)≤t) (hu : t≤(13/16 : ℝ))
    (hd : (247/720 : ℝ)≤d) (he : d≤(13/36 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(1152602/1233225 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_449 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (25/32 : ℝ)≤t) (hu : t≤(13/16 : ℝ))
    (hd : (13/40 : ℝ)≤d) (he : d≤(13/36 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (247/720 : ℝ) with hm|hm
  · exact corner_grid_447 h hl hu hd hm
  · exact corner_grid_448 h hl hu hm.le he

private lemma corner_grid_450 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/4 : ℝ)≤t) (hu : t≤(13/16 : ℝ))
    (hd : (13/40 : ℝ)≤d) (he : d≤(13/36 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (25/32 : ℝ) with hm|hm
  · exact corner_grid_446 h hl hm hd he
  · exact corner_grid_449 h hm.le hu hd he

private lemma corner_grid_451 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/4 : ℝ)≤t) (hu : t≤(13/16 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(13/36 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (13/40 : ℝ) with hm|hm
  · exact corner_grid_443 h hl hu hd hm
  · exact corner_grid_450 h hl hu hm.le he

private lemma corner_grid_452 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (13/16 : ℝ)≤t) (hu : t≤(27/32 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(221/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(4746368/4181625 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_453 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (13/16 : ℝ)≤t) (hu : t≤(27/32 : ℝ))
    (hd : (221/720 : ℝ)≤d) (he : d≤(13/40 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(4255592/4181625 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_454 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (13/16 : ℝ)≤t) (hu : t≤(27/32 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(13/40 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (221/720 : ℝ) with hm|hm
  · exact corner_grid_452 h hl hu hd hm
  · exact corner_grid_453 h hl hu hm.le he

private lemma corner_grid_455 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (27/32 : ℝ)≤t) (hu : t≤(7/8 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(221/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(207548/212625 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_456 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (27/32 : ℝ)≤t) (hu : t≤(7/8 : ℝ))
    (hd : (221/720 : ℝ)≤d) (he : d≤(13/40 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(353749/425250 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_457 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (27/32 : ℝ)≤t) (hu : t≤(7/8 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(13/40 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (221/720 : ℝ) with hm|hm
  · exact corner_grid_455 h hl hu hd hm
  · exact corner_grid_456 h hl hu hm.le he

private lemma corner_grid_458 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (13/16 : ℝ)≤t) (hu : t≤(7/8 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(13/40 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (27/32 : ℝ) with hm|hm
  · exact corner_grid_454 h hl hm hd he
  · exact corner_grid_457 h hm.le hu hd he

private lemma corner_grid_459 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (13/16 : ℝ)≤t) (hu : t≤(27/32 : ℝ))
    (hd : (13/40 : ℝ)≤d) (he : d≤(247/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(46112/51625 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_460 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (13/16 : ℝ)≤t) (hu : t≤(27/32 : ℝ))
    (hd : (247/720 : ℝ)≤d) (he : d≤(13/36 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(3184808/4181625 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_461 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (13/16 : ℝ)≤t) (hu : t≤(27/32 : ℝ))
    (hd : (13/40 : ℝ)≤d) (he : d≤(13/36 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (247/720 : ℝ) with hm|hm
  · exact corner_grid_459 h hl hu hd hm
  · exact corner_grid_460 h hl hu hm.le he

private lemma corner_grid_462 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (27/32 : ℝ)≤t) (hu : t≤(7/8 : ℝ))
    (hd : (13/40 : ℝ)≤d) (he : d≤(247/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(594/875 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_463 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (27/32 : ℝ)≤t) (hu : t≤(7/8 : ℝ))
    (hd : (247/720 : ℝ)≤d) (he : d≤(13/36 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(219901/425250 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_464 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (27/32 : ℝ)≤t) (hu : t≤(7/8 : ℝ))
    (hd : (13/40 : ℝ)≤d) (he : d≤(13/36 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (247/720 : ℝ) with hm|hm
  · exact corner_grid_462 h hl hu hd hm
  · exact corner_grid_463 h hl hu hm.le he

private lemma corner_grid_465 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (13/16 : ℝ)≤t) (hu : t≤(7/8 : ℝ))
    (hd : (13/40 : ℝ)≤d) (he : d≤(13/36 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (27/32 : ℝ) with hm|hm
  · exact corner_grid_461 h hl hm hd he
  · exact corner_grid_464 h hm.le hu hd he

private lemma corner_grid_466 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (13/16 : ℝ)≤t) (hu : t≤(7/8 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(13/36 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (13/40 : ℝ) with hm|hm
  · exact corner_grid_458 h hl hu hd hm
  · exact corner_grid_465 h hl hu hm.le he

private lemma corner_grid_467 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/4 : ℝ)≤t) (hu : t≤(7/8 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(13/36 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (13/16 : ℝ) with hm|hm
  · exact corner_grid_451 h hl hm hd he
  · exact corner_grid_466 h hm.le hu hd he

private lemma corner_grid_468 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/4 : ℝ)≤t) (hu : t≤(25/32 : ℝ))
    (hd : (13/36 : ℝ)≤d) (he : d≤(91/240 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(218240/226233 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_469 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/4 : ℝ)≤t) (hu : t≤(25/32 : ℝ))
    (hd : (91/240 : ℝ)≤d) (he : d≤(143/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(538472/628425 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_470 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/4 : ℝ)≤t) (hu : t≤(25/32 : ℝ))
    (hd : (13/36 : ℝ)≤d) (he : d≤(143/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (91/240 : ℝ) with hm|hm
  · exact corner_grid_468 h hl hu hd hm
  · exact corner_grid_469 h hl hu hm.le he

private lemma corner_grid_471 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (25/32 : ℝ)≤t) (hu : t≤(13/16 : ℝ))
    (hd : (13/36 : ℝ)≤d) (he : d≤(91/240 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(40304/49329 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_472 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (25/32 : ℝ)≤t) (hu : t≤(13/16 : ℝ))
    (hd : (91/240 : ℝ)≤d) (he : d≤(143/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(13574/19575 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_473 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (25/32 : ℝ)≤t) (hu : t≤(13/16 : ℝ))
    (hd : (13/36 : ℝ)≤d) (he : d≤(143/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (91/240 : ℝ) with hm|hm
  · exact corner_grid_471 h hl hu hd hm
  · exact corner_grid_472 h hl hu hm.le he

private lemma corner_grid_474 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/4 : ℝ)≤t) (hu : t≤(13/16 : ℝ))
    (hd : (13/36 : ℝ)≤d) (he : d≤(143/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (25/32 : ℝ) with hm|hm
  · exact corner_grid_470 h hl hm hd he
  · exact corner_grid_473 h hm.le hu hd he

private lemma corner_grid_475 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/4 : ℝ)≤t) (hu : t≤(25/32 : ℝ))
    (hd : (143/360 : ℝ)≤d) (he : d≤(299/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(221408/297675 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_476 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/4 : ℝ)≤t) (hu : t≤(25/32 : ℝ))
    (hd : (299/720 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(3537512/5655825 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_477 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/4 : ℝ)≤t) (hu : t≤(25/32 : ℝ))
    (hd : (143/360 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (299/720 : ℝ) with hm|hm
  · exact corner_grid_475 h hl hu hd hm
  · exact corner_grid_476 h hl hu hm.le he

private lemma corner_grid_478 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (25/32 : ℝ)≤t) (hu : t≤(13/16 : ℝ))
    (hd : (143/360 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(695288/1233225 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_479 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/4 : ℝ)≤t) (hu : t≤(13/16 : ℝ))
    (hd : (143/360 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (25/32 : ℝ) with hm|hm
  · exact corner_grid_477 h hl hm hd he
  · exact corner_grid_478 h hm.le hu hd he

private lemma corner_grid_480 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/4 : ℝ)≤t) (hu : t≤(13/16 : ℝ))
    (hd : (13/36 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (143/360 : ℝ) with hm|hm
  · exact corner_grid_474 h hl hu hd hm
  · exact corner_grid_479 h hl hu hm.le he

private lemma corner_grid_481 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (13/16 : ℝ)≤t) (hu : t≤(27/32 : ℝ))
    (hd : (13/36 : ℝ)≤d) (he : d≤(91/240 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(104192/167265 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_482 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (13/16 : ℝ)≤t) (hu : t≤(27/32 : ℝ))
    (hd : (91/240 : ℝ)≤d) (he : d≤(143/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(221672/464625 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_483 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (13/16 : ℝ)≤t) (hu : t≤(27/32 : ℝ))
    (hd : (13/36 : ℝ)≤d) (he : d≤(143/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (91/240 : ℝ) with hm|hm
  · exact corner_grid_481 h hl hu hd hm
  · exact corner_grid_482 h hl hu hm.le he

private lemma corner_grid_484 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (27/32 : ℝ)≤t) (hu : t≤(7/8 : ℝ))
    (hd : (13/36 : ℝ)≤d) (he : d≤(143/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(2948/8505 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_485 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (13/16 : ℝ)≤t) (hu : t≤(7/8 : ℝ))
    (hd : (13/36 : ℝ)≤d) (he : d≤(143/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (27/32 : ℝ) with hm|hm
  · exact corner_grid_483 h hl hm hd he
  · exact corner_grid_484 h hm.le hu hd he

private lemma corner_grid_486 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (13/16 : ℝ)≤t) (hu : t≤(27/32 : ℝ))
    (hd : (143/360 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(1355552/4181625 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_487 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (27/32 : ℝ)≤t) (_hu : t≤(7/8 : ℝ))
    (hd : (143/360 : ℝ)≤d) (_he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  nlinarith only [h.dbound,h.d0,hd,hl]

private lemma corner_grid_488 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (13/16 : ℝ)≤t) (hu : t≤(7/8 : ℝ))
    (hd : (143/360 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (27/32 : ℝ) with hm|hm
  · exact corner_grid_486 h hl hm hd he
  · exact corner_grid_487 h hm.le hu hd he

private lemma corner_grid_489 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (13/16 : ℝ)≤t) (hu : t≤(7/8 : ℝ))
    (hd : (13/36 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (143/360 : ℝ) with hm|hm
  · exact corner_grid_485 h hl hu hd hm
  · exact corner_grid_488 h hl hu hm.le he

private lemma corner_grid_490 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/4 : ℝ)≤t) (hu : t≤(7/8 : ℝ))
    (hd : (13/36 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (13/16 : ℝ) with hm|hm
  · exact corner_grid_480 h hl hm hd he
  · exact corner_grid_489 h hm.le hu hd he

private lemma corner_grid_491 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/4 : ℝ)≤t) (hu : t≤(7/8 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (13/36 : ℝ) with hm|hm
  · exact corner_grid_467 h hl hu hd hm
  · exact corner_grid_490 h hl hu hm.le he

private lemma corner_grid_492 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/8 : ℝ)≤t) (hu : t≤(29/32 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(221/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(1895168/2594025 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_493 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/8 : ℝ)≤t) (hu : t≤(29/32 : ℝ))
    (hd : (221/720 : ℝ)≤d) (he : d≤(13/40 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(1404392/2594025 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_494 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/8 : ℝ)≤t) (hu : t≤(29/32 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(13/40 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (221/720 : ℝ) with hm|hm
  · exact corner_grid_492 h hl hu hd hm
  · exact corner_grid_493 h hl hu hm.le he

private lemma corner_grid_495 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (29/32 : ℝ)≤t) (hu : t≤(15/16 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(13/40 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(117392/439425 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_496 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/8 : ℝ)≤t) (hu : t≤(15/16 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(13/40 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (29/32 : ℝ) with hm|hm
  · exact corner_grid_494 h hl hm hd he
  · exact corner_grid_495 h hm.le hu hd he

private lemma corner_grid_497 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/8 : ℝ)≤t) (hu : t≤(29/32 : ℝ))
    (hd : (13/40 : ℝ)≤d) (he : d≤(13/36 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(10912/32025 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_498 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (29/32 : ℝ)≤t) (_hu : t≤(15/16 : ℝ))
    (hd : (13/40 : ℝ)≤d) (_he : d≤(13/36 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  nlinarith only [h.dbound,h.d0,hd,hl]

private lemma corner_grid_499 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/8 : ℝ)≤t) (hu : t≤(15/16 : ℝ))
    (hd : (13/40 : ℝ)≤d) (he : d≤(13/36 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (29/32 : ℝ) with hm|hm
  · exact corner_grid_497 h hl hm hd he
  · exact corner_grid_498 h hm.le hu hd he

private lemma corner_grid_500 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/8 : ℝ)≤t) (hu : t≤(15/16 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(13/36 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (13/40 : ℝ) with hm|hm
  · exact corner_grid_496 h hl hu hd hm
  · exact corner_grid_499 h hl hu hm.le he

private lemma corner_grid_501 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (15/16 : ℝ)≤t) (_hu : t≤(1/1 : ℝ))
    (hd : (13/45 : ℝ)≤d) (_he : d≤(13/36 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  nlinarith only [h.dbound,h.d0,hd,hl]

private lemma corner_grid_502 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/8 : ℝ)≤t) (hu : t≤(1/1 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(13/36 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (15/16 : ℝ) with hm|hm
  · exact corner_grid_500 h hl hm hd he
  · exact corner_grid_501 h hm.le hu hd he

private lemma corner_grid_503 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/8 : ℝ)≤t) (_hu : t≤(1/1 : ℝ))
    (hd : (13/36 : ℝ)≤d) (_he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  nlinarith only [h.dbound,h.d0,hd,hl]

private lemma corner_grid_504 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/8 : ℝ)≤t) (hu : t≤(1/1 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (13/36 : ℝ) with hm|hm
  · exact corner_grid_502 h hl hu hd hm
  · exact corner_grid_503 h hl hu hm.le he

private lemma corner_grid_505 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/4 : ℝ)≤t) (hu : t≤(1/1 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (7/8 : ℝ) with hm|hm
  · exact corner_grid_491 h hl hm hd he
  · exact corner_grid_504 h hm.le hu hd he

private lemma corner_grid_506 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/4 : ℝ)≤t) (hu : t≤(25/32 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(169/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(45056/89775 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_507 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (25/32 : ℝ)≤t) (hu : t≤(13/16 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(169/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(39248/137025 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_508 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/4 : ℝ)≤t) (hu : t≤(13/16 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(169/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (25/32 : ℝ) with hm|hm
  · exact corner_grid_506 h hl hm hd he
  · exact corner_grid_507 h hm.le hu hd he

private lemma corner_grid_509 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/4 : ℝ)≤t) (hu : t≤(25/32 : ℝ))
    (hd : (169/360 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(1351328/5655825 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_510 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (25/32 : ℝ)≤t) (_hu : t≤(13/16 : ℝ))
    (hd : (169/360 : ℝ)≤d) (_he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  nlinarith only [h.dbound,h.d0,hd,hl]

private lemma corner_grid_511 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/4 : ℝ)≤t) (hu : t≤(13/16 : ℝ))
    (hd : (169/360 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (25/32 : ℝ) with hm|hm
  · exact corner_grid_509 h hl hm hd he
  · exact corner_grid_510 h hm.le hu hd he

private lemma corner_grid_512 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/4 : ℝ)≤t) (hu : t≤(13/16 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (169/360 : ℝ) with hm|hm
  · exact corner_grid_508 h hl hu hd hm
  · exact corner_grid_511 h hl hu hm.le he

private lemma corner_grid_513 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (13/16 : ℝ)≤t) (_hu : t≤(7/8 : ℝ))
    (hd : (13/30 : ℝ)≤d) (_he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  nlinarith only [h.dbound,h.d0,hd,hl]

private lemma corner_grid_514 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/4 : ℝ)≤t) (hu : t≤(7/8 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (13/16 : ℝ) with hm|hm
  · exact corner_grid_512 h hl hm hd he
  · exact corner_grid_513 h hm.le hu hd he

private lemma corner_grid_515 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/4 : ℝ)≤t) (_hu : t≤(7/8 : ℝ))
    (hd : (91/180 : ℝ)≤d) (_he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  nlinarith only [h.dbound,h.d0,hd,hl]

private lemma corner_grid_516 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/4 : ℝ)≤t) (hu : t≤(7/8 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (91/180 : ℝ) with hm|hm
  · exact corner_grid_514 h hl hu hd hm
  · exact corner_grid_515 h hl hu hm.le he

private lemma corner_grid_517 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/8 : ℝ)≤t) (_hu : t≤(1/1 : ℝ))
    (hd : (13/30 : ℝ)≤d) (_he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  nlinarith only [h.dbound,h.d0,hd,hl]

private lemma corner_grid_518 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/4 : ℝ)≤t) (hu : t≤(1/1 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (7/8 : ℝ) with hm|hm
  · exact corner_grid_516 h hl hm hd he
  · exact corner_grid_517 h hm.le hu hd he

private lemma corner_grid_519 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/4 : ℝ)≤t) (hu : t≤(1/1 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (13/30 : ℝ) with hm|hm
  · exact corner_grid_505 h hl hu hd hm
  · exact corner_grid_518 h hl hu hm.le he

private lemma corner_grid_520 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/2 : ℝ)≤t) (hu : t≤(1/1 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (3/4 : ℝ) with hm|hm
  · exact corner_grid_438 h hl hm hd he
  · exact corner_grid_519 h hm.le hu hd he

private lemma corner_grid_521 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/2 : ℝ)≤t) (hu : t≤(1/1 : ℝ))
    (hd : (0/1 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (13/45 : ℝ) with hm|hm
  · exact corner_grid_269 h hl hu hd hm
  · exact corner_grid_520 h hl hu hm.le he

private lemma corner_grid_522 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (0/1 : ℝ)≤t) (hu : t≤(1/1 : ℝ))
    (hd : (0/1 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (1/2 : ℝ) with hm|hm
  · exact corner_grid_202 h hl hm hd he
  · exact corner_grid_521 h hm.le hu hd he

theorem corner_root_strict {t d x : ℝ} (h : CornerRootData t d x) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  exact corner_grid_522 h (by simpa using h.t0) (by simpa using h.t1.le) (by simpa using h.d0) (by nlinarith only [h.d0,h.d3])
end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set
namespace CubicTorus

theorem fourCorner_normalized_contradiction_oai {A h b r s a V : ℝ}
    (hA0 : 0<A) (ha : 0<a) (ha1 : a≤1) (hA : A≤a) (hva : V=a^2/Real.pi) (hh : 0≤h)
    (hb0 : 0≤b) (hb1 : b<1) (hr0 : 0 ≤ r) (hr1 : r≤V)
    (hs1 : s≤1)
    (htop : Real.sqrt (Real.pi*r)≤A*b-h*(V-r))
    (hbottom : Real.sqrt (Real.pi*(1-s))≤A*b+h*(s-V))
    (hdrop : s-r≤A*Real.sqrt (1-b))
    (hbmax : 2/3≤b) (hxcap : h*A≤7/4) : False := by
  let x := h*A
  let d := Real.sqrt (1-b)
  let w := Real.sqrt (Real.pi*r)/a
  have hp : Real.pi≠0 := Real.pi_pos.ne'
  have haA : A≤a := hA
  have hx0 : 0≤x := mul_nonneg hh hA0.le
  have hd0 : 0≤d := Real.sqrt_nonneg _
  have hd2 : d^2=1-b := Real.sq_sqrt (by linarith)
  have hw0 : 0≤w := div_nonneg (Real.sqrt_nonneg _) ha.le
  have haw : a*w=Real.sqrt (Real.pi*r) := by dsimp only [w]; field_simp
  have hrw : r=a^2*w^2/Real.pi := by
    have hz := Real.sq_sqrt (mul_nonneg Real.pi_pos.le hr0)
    rw [← haw,mul_pow] at hz
    apply (eq_div_iff hp).mpr
    nlinarith only [hz]
  have hw1 : w≤1 := by
    rw [hva,hrw] at hr1
    have hz := (div_le_div_iff_of_pos_right Real.pi_pos).mp hr1
    have ha2 := sq_pos_of_pos ha
    have hw2' : w^2≤1 := (mul_le_mul_iff_right₀ ha2).mp (by simpa only [mul_one] using hz)
    nlinarith only [hw2',hw0]
  have hw2 : 0≤1-w^2 := by nlinarith
  have hxn : x≤h*a := mul_le_mul_of_nonneg_left haA hh
  have hnorm : w+x/Real.pi*(1-w^2)≤b := by
    have hleft := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hxn Real.pi_pos.le) hw2
    have hleft' := mul_le_mul_of_nonneg_left (add_le_add (le_refl w) hleft) ha.le
    have ht : a*(w+h*a/Real.pi*(1-w^2))≤A*b := by
      have hid : a*(w+h*a/Real.pi*(1-w^2))=a*w+h*(V-r) := by
        rw [hva,hrw]
        ring
      rw [hid,haw]
      linarith only [htop]
    have hright := mul_le_mul_of_nonneg_right haA hb0
    exact (mul_le_mul_iff_right₀ ha).mp (hleft'.trans (ht.trans hright))
  let f : ℝ → ℝ := fun t => t+x/Real.pi*(1-t^2)
  have hf : Continuous f := by fun_prop
  have hf1 : f 1=1 := by dsimp [f]; ring
  obtain ⟨t,ht,hft⟩ := intermediate_value_Icc hw1 hf.continuousOn
    (show b∈Icc (f w) (f 1) from ⟨hnorm,by rw [hf1]; exact hb1.le⟩)
  have ht0 : 0≤t := hw0.trans ht.1
  have ht1 : t<1 := by
    by_contra hn
    have he : t=1 := le_antisymm ht.2 (le_of_not_gt hn)
    rw [he,hf1] at hft
    linarith
  have htden : 0<1-t^2 := by nlinarith
  have hroot : t+x/Real.pi*(1-t^2)=b := hft
  have hxterm : 0≤x/Real.pi*(1-t^2) := by positivity
  have htd : t+d^2≤1 := by linarith only [hroot,hxterm,hd2]
  have hxroot : x=Real.pi*(1-t-d^2)/(1-t^2) := by
    apply (eq_div_iff htden.ne').mpr
    have he := congrArg (fun y : ℝ => y*Real.pi) hroot
    field_simp at he
    rw [show 1-t-d^2=b-t by linarith only [hd2]]
    nlinarith only [he]
  have hwtsq : w^2≤t^2 := (sq_le_sq₀ hw0 ht0).mpr ht.1
  have hrbound : r≤a^2*t^2/Real.pi := by
    rw [hrw]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hwtsq (sq_nonneg a)) Real.pi_pos.le
  have hEt : A*b-h*(V-a^2*t^2/Real.pi)≤a*t := by
    have he : A*b-h*(V-a^2*t^2/Real.pi)=
        A*t+(h/Real.pi)*(A^2-a^2)*(1-t^2) := by
      rw [hva,← hroot]
      dsimp only [x]
      ring
    have hA2 : A^2≤a^2 := (sq_le_sq₀ hA0.le ha.le).mpr haA
    have hcorr : (h/Real.pi)*(A^2-a^2)*(1-t^2)≤0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (div_nonneg hh Real.pi_pos.le) (sub_nonpos.mpr hA2)) htden.le
    rw [he]
    have hat := mul_le_mul_of_nonneg_right haA ht0
    linarith only [hcorr,hat]
  have hsb : s≤a^2*t^2/Real.pi+a*d := by
    have hAd := mul_le_mul_of_nonneg_right haA hd0
    linarith only [hdrop,hrbound,hAd]
  have hbottom' : Real.sqrt (Real.pi*(1-s))≤a*t+x*d := by
    have hdiff := mul_le_mul_of_nonneg_left hdrop hh
    have hrr := mul_le_mul_of_nonneg_left hrbound hh
    have hxd : h*(A*d)=x*d := by dsimp [x]; ring
    rw [hxd] at hdiff
    linarith only [hbottom,hdiff,hrr,hEt]
  have hbsq : Real.pi*(1-s)≤(a*t+x*d)^2 := by
    have hy : 0≤a*t+x*d := by positivity
    have hh' := (sq_le_sq₀ (Real.sqrt_nonneg (Real.pi*(1-s))) hy).mpr hbottom'
    rwa [Real.sq_sqrt (mul_nonneg Real.pi_pos.le (by linarith : 0≤1-s))] at hh'
  have hnec : 1≤a*d+(a^2*t^2+(a*t+x*d)^2)/Real.pi := by
    have hh' := mul_le_mul_of_nonneg_left hsb Real.pi_pos.le
    have hcancel : Real.pi*(a^2*t^2/Real.pi+a*d)=a^2*t^2+Real.pi*a*d := by field_simp
    rw [hcancel] at hh'
    have hh2 : 1≤((a*d)*Real.pi+(a^2*t^2+(a*t+x*d)^2))/Real.pi :=
      (le_div_iff₀ Real.pi_pos).mpr (by nlinarith only [hh',hbsq])
    simpa only [add_div,mul_div_cancel_right₀ _ hp] using hh2
  have hd3 : d^2≤1/3 := by linarith only [hd2,hbmax]
  have hroot' : Real.pi*(1-t-d^2)=x*(1-t^2) := by
    exact ((eq_div_iff htden.ne').mp hxroot).symm
  have hstrict := corner_root_strict (show CornerRootData t d x from
    ⟨ht0,ht1,hd0,hd3,hx0,hxcap,hroot'⟩)
  have hnec' : 1≤d+(t^2+(t+x*d)^2)/Real.pi := by
    have had := mul_le_mul_of_nonneg_right ha1 hd0
    have hat : a*t≤t := by simpa using mul_le_mul_of_nonneg_right ha1 ht0
    have hatsq : a^2*t^2≤t^2 := by
      simpa only [mul_pow] using (sq_le_sq₀ (mul_nonneg ha.le ht0) ht0).mpr hat
    have hsum : (a*t+x*d)^2≤(t+x*d)^2 := by
      have hat0 : 0≤a*t+x*d := by positivity
      have hxd0 : 0≤x*d := by positivity
      exact (sq_le_sq₀ hat0 (add_nonneg ht0 hxd0)).mpr (add_le_add hat (le_refl (x*d)))
    have hdiv := div_le_div_of_nonneg_right (add_le_add hatsq hsum) Real.pi_pos.le
    linarith only [hnec,had,hdiv]
  exact (not_lt_of_ge hnec') hstrict

end CubicTorus

end
end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.fourCorner_normalized_contradiction_oai := @OAI.CubicTorus.fourCorner_normalized_contradiction_oai
