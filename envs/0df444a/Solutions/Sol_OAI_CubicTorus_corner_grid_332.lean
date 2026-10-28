-- Prove2me | solution 1 for OAI.CubicTorus.corner_grid_332
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T17:21:20.31786+00:00
-- url     : https://prove2.me/submissions/490a88e0-6c96-4f82-9dae-e5042b3b8c0f

import Mathlib
import Definitions.Def_OAIQ079A000

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

private lemma corner_grid_270 {t d x : ℝ} (h : CornerRootData t d x)
    (_hl : (1/2 : ℝ)≤t) (hu : t≤(5/8 : ℝ))
    (_hd : (13/45 : ℝ)≤d) (he : d≤(13/36 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(7/4 : ℝ) := h.xcap
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_271 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/2 : ℝ)≤t) (hu : t≤(9/16 : ℝ))
    (hd : (13/36 : ℝ)≤d) (he : d≤(143/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(168608/99225 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_272 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/2 : ℝ)≤t) (hu : t≤(17/32 : ℝ))
    (hd : (143/360 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(15611552/10418625 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_273 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (17/32 : ℝ)≤t) (hu : t≤(9/16 : ℝ))
    (hd : (143/360 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(3546488/2480625 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_274 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/2 : ℝ)≤t) (hu : t≤(9/16 : ℝ))
    (hd : (143/360 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (17/32 : ℝ) with hm|hm
  · exact corner_grid_272 h hl hm hd he
  · exact corner_grid_273 h hm.le hu hd he

private lemma corner_grid_275 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/2 : ℝ)≤t) (hu : t≤(9/16 : ℝ))
    (hd : (13/36 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (143/360 : ℝ) with hm|hm
  · exact corner_grid_271 h hl hu hd hm
  · exact corner_grid_274 h hl hu hm.le he

private lemma corner_grid_276 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/16 : ℝ)≤t) (hu : t≤(19/32 : ℝ))
    (hd : (13/36 : ℝ)≤d) (he : d≤(143/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(560384/375921 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_277 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (19/32 : ℝ)≤t) (hu : t≤(5/8 : ℝ))
    (hd : (13/36 : ℝ)≤d) (he : d≤(143/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(2420/1701 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_278 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/16 : ℝ)≤t) (hu : t≤(5/8 : ℝ))
    (hd : (13/36 : ℝ)≤d) (he : d≤(143/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (19/32 : ℝ) with hm|hm
  · exact corner_grid_276 h hl hm hd he
  · exact corner_grid_277 h hm.le hu hd he

private lemma corner_grid_279 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/16 : ℝ)≤t) (hu : t≤(19/32 : ℝ))
    (hd : (143/360 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(12760352/9398025 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_280 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (19/32 : ℝ)≤t) (hu : t≤(5/8 : ℝ))
    (hd : (143/360 : ℝ)≤d) (he : d≤(299/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(54494/42525 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_281 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (19/32 : ℝ)≤t) (hu : t≤(5/8 : ℝ))
    (hd : (299/720 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(102553/85050 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_282 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (19/32 : ℝ)≤t) (hu : t≤(5/8 : ℝ))
    (hd : (143/360 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (299/720 : ℝ) with hm|hm
  · exact corner_grid_280 h hl hu hd hm
  · exact corner_grid_281 h hl hu hm.le he

private lemma corner_grid_283 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/16 : ℝ)≤t) (hu : t≤(5/8 : ℝ))
    (hd : (143/360 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (19/32 : ℝ) with hm|hm
  · exact corner_grid_279 h hl hm hd he
  · exact corner_grid_282 h hm.le hu hd he

private lemma corner_grid_284 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/16 : ℝ)≤t) (hu : t≤(5/8 : ℝ))
    (hd : (13/36 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (143/360 : ℝ) with hm|hm
  · exact corner_grid_278 h hl hu hd hm
  · exact corner_grid_283 h hl hu hm.le he

private lemma corner_grid_285 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/2 : ℝ)≤t) (hu : t≤(5/8 : ℝ))
    (hd : (13/36 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (9/16 : ℝ) with hm|hm
  · exact corner_grid_275 h hl hm hd he
  · exact corner_grid_284 h hm.le hu hd he

private lemma corner_grid_286 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/2 : ℝ)≤t) (hu : t≤(5/8 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (13/36 : ℝ) with hm|hm
  · exact corner_grid_270 h hl hu hd hm
  · exact corner_grid_285 h hl hu hm.le he

private lemma corner_grid_287 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/8 : ℝ)≤t) (hu : t≤(11/16 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(13/40 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(3324992/1913625 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_288 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/8 : ℝ)≤t) (hu : t≤(21/32 : ℝ))
    (hd : (13/40 : ℝ)≤d) (he : d≤(13/36 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(13792/9275 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_289 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (21/32 : ℝ)≤t) (hu : t≤(11/16 : ℝ))
    (hd : (13/40 : ℝ)≤d) (he : d≤(13/36 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(11176/7875 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_290 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/8 : ℝ)≤t) (hu : t≤(11/16 : ℝ))
    (hd : (13/40 : ℝ)≤d) (he : d≤(13/36 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (21/32 : ℝ) with hm|hm
  · exact corner_grid_288 h hl hm hd he
  · exact corner_grid_289 h hm.le hu hd he

private lemma corner_grid_291 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/8 : ℝ)≤t) (hu : t≤(11/16 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(13/36 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (13/40 : ℝ) with hm|hm
  · exact corner_grid_287 h hl hu hd hm
  · exact corner_grid_290 h hl hu hm.le he

private lemma corner_grid_292 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/16 : ℝ)≤t) (hu : t≤(23/32 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(13/40 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(949888/637875 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_293 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (23/32 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(13/40 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(20141/14175 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_294 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/16 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(13/40 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (23/32 : ℝ) with hm|hm
  · exact corner_grid_292 h hl hm hd he
  · exact corner_grid_293 h hm.le hu hd he

private lemma corner_grid_295 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/16 : ℝ)≤t) (hu : t≤(23/32 : ℝ))
    (hd : (13/40 : ℝ)≤d) (he : d≤(13/36 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(10592/7875 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_296 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (23/32 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (13/40 : ℝ)≤d) (he : d≤(247/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(3091/2450 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_297 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (23/32 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (247/720 : ℝ)≤d) (he : d≤(13/36 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(133243/113400 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_298 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (23/32 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (13/40 : ℝ)≤d) (he : d≤(13/36 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (247/720 : ℝ) with hm|hm
  · exact corner_grid_296 h hl hu hd hm
  · exact corner_grid_297 h hl hu hm.le he

private lemma corner_grid_299 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/16 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (13/40 : ℝ)≤d) (he : d≤(13/36 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (23/32 : ℝ) with hm|hm
  · exact corner_grid_295 h hl hm hd he
  · exact corner_grid_298 h hm.le hu hd he

private lemma corner_grid_300 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/16 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(13/36 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (13/40 : ℝ) with hm|hm
  · exact corner_grid_294 h hl hu hd hm
  · exact corner_grid_299 h hl hu hm.le he

private lemma corner_grid_301 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/8 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(13/36 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (11/16 : ℝ) with hm|hm
  · exact corner_grid_291 h hl hm hd he
  · exact corner_grid_300 h hm.le hu hd he

private lemma corner_grid_302 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/8 : ℝ)≤t) (hu : t≤(21/32 : ℝ))
    (hd : (13/36 : ℝ)≤d) (he : d≤(143/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(40576/30051 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_303 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (21/32 : ℝ)≤t) (hu : t≤(11/16 : ℝ))
    (hd : (13/36 : ℝ)≤d) (he : d≤(91/240 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(13904/10935 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_304 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (21/32 : ℝ)≤t) (hu : t≤(11/16 : ℝ))
    (hd : (91/240 : ℝ)≤d) (he : d≤(143/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(253418/212625 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_305 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (21/32 : ℝ)≤t) (hu : t≤(11/16 : ℝ))
    (hd : (13/36 : ℝ)≤d) (he : d≤(143/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (91/240 : ℝ) with hm|hm
  · exact corner_grid_303 h hl hu hd hm
  · exact corner_grid_304 h hl hu hm.le he

private lemma corner_grid_306 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/8 : ℝ)≤t) (hu : t≤(11/16 : ℝ))
    (hd : (13/36 : ℝ)≤d) (he : d≤(143/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (21/32 : ℝ) with hm|hm
  · exact corner_grid_302 h hl hm hd he
  · exact corner_grid_305 h hm.le hu hd he

private lemma corner_grid_307 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/8 : ℝ)≤t) (hu : t≤(21/32 : ℝ))
    (hd : (143/360 : ℝ)≤d) (he : d≤(299/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(900832/751275 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_308 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/8 : ℝ)≤t) (hu : t≤(21/32 : ℝ))
    (hd : (299/720 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(839992/751275 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_309 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/8 : ℝ)≤t) (hu : t≤(21/32 : ℝ))
    (hd : (143/360 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (299/720 : ℝ) with hm|hm
  · exact corner_grid_307 h hl hu hd hm
  · exact corner_grid_308 h hl hu hm.le he

private lemma corner_grid_310 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (21/32 : ℝ)≤t) (hu : t≤(11/16 : ℝ))
    (hd : (143/360 : ℝ)≤d) (he : d≤(299/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(302984/273375 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_311 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (21/32 : ℝ)≤t) (hu : t≤(11/16 : ℝ))
    (hd : (299/720 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(1953578/1913625 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_312 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (21/32 : ℝ)≤t) (hu : t≤(11/16 : ℝ))
    (hd : (143/360 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (299/720 : ℝ) with hm|hm
  · exact corner_grid_310 h hl hu hd hm
  · exact corner_grid_311 h hl hu hm.le he

private lemma corner_grid_313 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/8 : ℝ)≤t) (hu : t≤(11/16 : ℝ))
    (hd : (143/360 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (21/32 : ℝ) with hm|hm
  · exact corner_grid_309 h hl hm hd he
  · exact corner_grid_312 h hm.le hu hd he

private lemma corner_grid_314 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/8 : ℝ)≤t) (hu : t≤(11/16 : ℝ))
    (hd : (13/36 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (143/360 : ℝ) with hm|hm
  · exact corner_grid_306 h hl hu hd hm
  · exact corner_grid_313 h hl hu hm.le he

private lemma corner_grid_315 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/16 : ℝ)≤t) (hu : t≤(23/32 : ℝ))
    (hd : (13/36 : ℝ)≤d) (he : d≤(91/240 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(30208/25515 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_316 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/16 : ℝ)≤t) (hu : t≤(23/32 : ℝ))
    (hd : (91/240 : ℝ)≤d) (he : d≤(143/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(77752/70875 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_317 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/16 : ℝ)≤t) (hu : t≤(23/32 : ℝ))
    (hd : (13/36 : ℝ)≤d) (he : d≤(143/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (91/240 : ℝ) with hm|hm
  · exact corner_grid_315 h hl hu hd hm
  · exact corner_grid_316 h hl hu hm.le he

private lemma corner_grid_318 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (23/32 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (13/36 : ℝ)≤d) (he : d≤(91/240 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(4301/3969 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_319 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (23/32 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (91/240 : ℝ)≤d) (he : d≤(143/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(87109/88200 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_320 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (23/32 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (13/36 : ℝ)≤d) (he : d≤(143/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (91/240 : ℝ) with hm|hm
  · exact corner_grid_318 h hl hu hd hm
  · exact corner_grid_319 h hl hu hm.le he

private lemma corner_grid_321 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/16 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (13/36 : ℝ)≤d) (he : d≤(143/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (23/32 : ℝ) with hm|hm
  · exact corner_grid_317 h hl hm hd he
  · exact corner_grid_320 h hm.le hu hd he

private lemma corner_grid_322 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/16 : ℝ)≤t) (hu : t≤(23/32 : ℝ))
    (hd : (143/360 : ℝ)≤d) (he : d≤(299/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(641632/637875 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_323 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/16 : ℝ)≤t) (hu : t≤(23/32 : ℝ))
    (hd : (299/720 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(580792/637875 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_324 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/16 : ℝ)≤t) (hu : t≤(23/32 : ℝ))
    (hd : (143/360 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (299/720 : ℝ) with hm|hm
  · exact corner_grid_322 h hl hu hd hm
  · exact corner_grid_323 h hl hu hm.le he

private lemma corner_grid_325 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (23/32 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (143/360 : ℝ)≤d) (he : d≤(299/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(176011/198450 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_326 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (23/32 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (299/720 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(12661/16200 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_327 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (23/32 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (143/360 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (299/720 : ℝ) with hm|hm
  · exact corner_grid_325 h hl hu hd hm
  · exact corner_grid_326 h hl hu hm.le he

private lemma corner_grid_328 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/16 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (143/360 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (23/32 : ℝ) with hm|hm
  · exact corner_grid_324 h hl hm hd he
  · exact corner_grid_327 h hm.le hu hd he

private lemma corner_grid_329 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/16 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (13/36 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (143/360 : ℝ) with hm|hm
  · exact corner_grid_321 h hl hu hd hm
  · exact corner_grid_328 h hl hu hm.le he

private lemma corner_grid_330 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/8 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (13/36 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (11/16 : ℝ) with hm|hm
  · exact corner_grid_314 h hl hm hd he
  · exact corner_grid_329 h hm.le hu hd he

private lemma corner_grid_331 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/8 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (13/36 : ℝ) with hm|hm
  · exact corner_grid_301 h hl hu hd hm
  · exact corner_grid_330 h hl hu hm.le he

lemma corner_grid_332_oai {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/2 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (5/8 : ℝ) with hm|hm
  · exact corner_grid_286 h hl hm hd he
  · exact corner_grid_331 h hm.le hu hd he

end CubicTorus
end
end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.corner_grid_332_oai := @OAI.CubicTorus.corner_grid_332_oai
