-- Prove2me | solution 1 for OAI.CubicTorus.corner_grid_202
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T17:18:49.639131+00:00
-- url     : https://prove2.me/submissions/2566b7a8-9299-4696-bfde-032282fc8de7

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

lemma corner_box_root_impossible {t d x l u E : ℝ}
    (ht0 : 0≤t) (hd0 : 0≤d) (_hx0 : 0≤x) (hx : x≤7/4)
    (he : Real.pi*(1-t-d^2)=x*(1-t^2))
    (hl : l≤t) (hl0 : 0≤l) (hu : t≤u) (hu1 : u≤1)
    (hE : d≤E) (he0 : 0≤1-u-E^2)
    (hnum : (7/4 : ℝ)*(1-l^2)<(157/50 : ℝ)*(1-u-E^2)) : False := by
  have hdE : d^2≤E^2 := by nlinarith
  have hlt : l^2≤t^2 := by nlinarith
  have ht1 : t^2≤1 := by nlinarith
  have ha := mul_le_mul_of_nonneg_right hx (sub_nonneg.mpr ht1)
  have hb := mul_nonneg (show (0 : ℝ)≤7/4 by norm_num) (sub_nonneg.mpr hlt)
  have hc := mul_nonneg Real.pi_pos.le (show 0≤u-t+(E^2-d^2) by linarith)
  have hp : (157/50 : ℝ)≤Real.pi := by linarith [Real.pi_gt_d4]
  have hq := mul_le_mul_of_nonneg_right hp he0
  nlinarith only [he,ha,hb,hc,hq,hnum]

end CubicTorus

end
end

section

noncomputable section
namespace CubicTorus

lemma corner_grid_0 {t d x : ℝ} (h : CornerRootData t d x)
    (_hl : (0/1 : ℝ)≤t) (hu : t≤(1/2 : ℝ))
    (_hd : (0/1 : ℝ)≤d) (he : d≤(13/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(7/4 : ℝ) := h.xcap
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

lemma corner_grid_1 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (0/1 : ℝ)≤t) (hu : t≤(1/4 : ℝ))
    (_hd : (13/45 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  exact (corner_box_root_impossible h.t0 h.d0 h.x0 h.xcap h.root
    hl (by norm_num) hu (by norm_num) he (by norm_num) (by norm_num)).elim

lemma corner_grid_2 {t d x : ℝ} (h : CornerRootData t d x)
    (_hl : (0/1 : ℝ)≤t) (hu : t≤(1/8 : ℝ))
    (_hd : (13/30 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(7/4 : ℝ) := h.xcap
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

lemma corner_grid_3 {t d x : ℝ} (h : CornerRootData t d x)
    (_hl : (1/8 : ℝ)≤t) (hu : t≤(1/4 : ℝ))
    (_hd : (13/30 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(7/4 : ℝ) := h.xcap
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

lemma corner_grid_4 {t d x : ℝ} (h : CornerRootData t d x)
    (_hl : (1/8 : ℝ)≤t) (hu : t≤(3/16 : ℝ))
    (_hd : (91/180 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(7/4 : ℝ) := h.xcap
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_5 {t d x : ℝ} (h : CornerRootData t d x)
    (_hl : (1/8 : ℝ)≤t) (hu : t≤(5/32 : ℝ))
    (_hd : (13/24 : ℝ)≤d) (he : d≤(403/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(7/4 : ℝ) := h.xcap
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_6 {t d x : ℝ} (h : CornerRootData t d x)
    (_hl : (1/8 : ℝ)≤t) (hu : t≤(9/64 : ℝ))
    (_hd : (403/720 : ℝ)≤d) (he : d≤(91/160 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(7/4 : ℝ) := h.xcap
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_7 {t d x : ℝ} (h : CornerRootData t d x)
    (_hl : (1/8 : ℝ)≤t) (hu : t≤(17/128 : ℝ))
    (_hd : (91/160 : ℝ)≤d) (he : d≤(1651/2880 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(7/4 : ℝ) := h.xcap
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_8 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/8 : ℝ)≤t) (hu : t≤(17/128 : ℝ))
    (hd : (1651/2880 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(398798312/228146625 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_9 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/8 : ℝ)≤t) (hu : t≤(17/128 : ℝ))
    (hd : (91/160 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (1651/2880 : ℝ) with hm|hm
  · exact corner_grid_7 h hl hu hd hm
  · exact corner_grid_8 h hl hu hm.le he

private lemma corner_grid_10 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (17/128 : ℝ)≤t) (hu : t≤(9/64 : ℝ))
    (hd : (91/160 : ℝ)≤d) (he : d≤(1651/2880 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(111352/63875 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_11 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (17/128 : ℝ)≤t) (hu : t≤(9/64 : ℝ))
    (hd : (1651/2880 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(8933998/5173875 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_12 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (17/128 : ℝ)≤t) (hu : t≤(9/64 : ℝ))
    (hd : (91/160 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (1651/2880 : ℝ) with hm|hm
  · exact corner_grid_10 h hl hu hd hm
  · exact corner_grid_11 h hl hu hm.le he

private lemma corner_grid_13 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/8 : ℝ)≤t) (hu : t≤(9/64 : ℝ))
    (hd : (91/160 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (17/128 : ℝ) with hm|hm
  · exact corner_grid_9 h hl hm hd he
  · exact corner_grid_12 h hm.le hu hd he

private lemma corner_grid_14 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/8 : ℝ)≤t) (hu : t≤(9/64 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (91/160 : ℝ) with hm|hm
  · exact corner_grid_6 h hl hu hd hm
  · exact corner_grid_13 h hl hu hm.le he

private lemma corner_grid_15 {t d x : ℝ} (h : CornerRootData t d x)
    (_hl : (9/64 : ℝ)≤t) (hu : t≤(5/32 : ℝ))
    (_hd : (403/720 : ℝ)≤d) (he : d≤(91/160 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(7/4 : ℝ) := h.xcap
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_16 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/64 : ℝ)≤t) (hu : t≤(19/128 : ℝ))
    (hd : (91/160 : ℝ)≤d) (he : d≤(1651/2880 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(1609696/934675 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_17 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/64 : ℝ)≤t) (hu : t≤(19/128 : ℝ))
    (hd : (1651/2880 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(387393512/227126025 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_18 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/64 : ℝ)≤t) (hu : t≤(19/128 : ℝ))
    (hd : (91/160 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (1651/2880 : ℝ) with hm|hm
  · exact corner_grid_16 h hl hu hd hm
  · exact corner_grid_17 h hl hu hm.le he

private lemma corner_grid_19 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (19/128 : ℝ)≤t) (hu : t≤(5/32 : ℝ))
    (hd : (91/160 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(297418/174825 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_20 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/64 : ℝ)≤t) (hu : t≤(5/32 : ℝ))
    (hd : (91/160 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (19/128 : ℝ) with hm|hm
  · exact corner_grid_18 h hl hm hd he
  · exact corner_grid_19 h hm.le hu hd he

private lemma corner_grid_21 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/64 : ℝ)≤t) (hu : t≤(5/32 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (91/160 : ℝ) with hm|hm
  · exact corner_grid_15 h hl hu hd hm
  · exact corner_grid_20 h hl hu hm.le he

private lemma corner_grid_22 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/8 : ℝ)≤t) (hu : t≤(5/32 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (9/64 : ℝ) with hm|hm
  · exact corner_grid_14 h hl hm hd he
  · exact corner_grid_21 h hm.le hu hd he

private lemma corner_grid_23 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/8 : ℝ)≤t) (hu : t≤(5/32 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (403/720 : ℝ) with hm|hm
  · exact corner_grid_5 h hl hu hd hm
  · exact corner_grid_22 h hl hu hm.le he

private lemma corner_grid_24 {t d x : ℝ} (h : CornerRootData t d x)
    (_hl : (5/32 : ℝ)≤t) (hu : t≤(11/64 : ℝ))
    (_hd : (13/24 : ℝ)≤d) (he : d≤(403/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(7/4 : ℝ) := h.xcap
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_25 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/64 : ℝ)≤t) (hu : t≤(3/16 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(793/1440 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(3872/2223 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_26 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/64 : ℝ)≤t) (hu : t≤(3/16 : ℝ))
    (hd : (793/1440 : ℝ)≤d) (he : d≤(403/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(11971861/7002450 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_27 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/64 : ℝ)≤t) (hu : t≤(3/16 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(403/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (793/1440 : ℝ) with hm|hm
  · exact corner_grid_25 h hl hu hd hm
  · exact corner_grid_26 h hl hu hm.le he

private lemma corner_grid_28 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/32 : ℝ)≤t) (hu : t≤(3/16 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(403/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (11/64 : ℝ) with hm|hm
  · exact corner_grid_24 h hl hm hd he
  · exact corner_grid_27 h hm.le hu hd he

private lemma corner_grid_29 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/32 : ℝ)≤t) (hu : t≤(11/64 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(91/160 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(96796832/56345625 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_30 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/32 : ℝ)≤t) (hu : t≤(21/128 : ℝ))
    (hd : (91/160 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(4688288/2790025 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_31 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (21/128 : ℝ)≤t) (hu : t≤(11/64 : ℝ))
    (hd : (91/160 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(384824/231875 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_32 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/32 : ℝ)≤t) (hu : t≤(11/64 : ℝ))
    (hd : (91/160 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (21/128 : ℝ) with hm|hm
  · exact corner_grid_30 h hl hm hd he
  · exact corner_grid_31 h hm.le hu hd he

private lemma corner_grid_33 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/32 : ℝ)≤t) (hu : t≤(11/64 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (91/160 : ℝ) with hm|hm
  · exact corner_grid_29 h hl hu hd hm
  · exact corner_grid_32 h hl hu hm.le he

private lemma corner_grid_34 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/64 : ℝ)≤t) (hu : t≤(3/16 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(91/160 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(5871602/3501225 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_35 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/64 : ℝ)≤t) (hu : t≤(23/128 : ℝ))
    (hd : (91/160 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(4547488/2774625 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_36 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (23/128 : ℝ)≤t) (hu : t≤(3/16 : ℝ))
    (hd : (91/160 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(19987/12350 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_37 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/64 : ℝ)≤t) (hu : t≤(3/16 : ℝ))
    (hd : (91/160 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (23/128 : ℝ) with hm|hm
  · exact corner_grid_35 h hl hm hd he
  · exact corner_grid_36 h hm.le hu hd he

private lemma corner_grid_38 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/64 : ℝ)≤t) (hu : t≤(3/16 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (91/160 : ℝ) with hm|hm
  · exact corner_grid_34 h hl hu hd hm
  · exact corner_grid_37 h hl hu hm.le he

private lemma corner_grid_39 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/32 : ℝ)≤t) (hu : t≤(3/16 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (11/64 : ℝ) with hm|hm
  · exact corner_grid_33 h hl hm hd he
  · exact corner_grid_38 h hm.le hu hd he

private lemma corner_grid_40 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/32 : ℝ)≤t) (hu : t≤(3/16 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (403/720 : ℝ) with hm|hm
  · exact corner_grid_28 h hl hu hd hm
  · exact corner_grid_39 h hl hu hm.le he

lemma corner_grid_41 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/8 : ℝ)≤t) (hu : t≤(3/16 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (5/32 : ℝ) with hm|hm
  · exact corner_grid_23 h hl hm hd he
  · exact corner_grid_40 h hm.le hu hd he

end CubicTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_CornerGrid42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace CubicTorus

private lemma corner_grid_42 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/8 : ℝ)≤t) (hu : t≤(3/16 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (13/24 : ℝ) with hm|hm
  · exact corner_grid_4 h hl hu hd hm
  · exact corner_grid_41 h hl hu hm.le he

private lemma corner_grid_43 {t d x : ℝ} (h : CornerRootData t d x)
    (_hl : (3/16 : ℝ)≤t) (hu : t≤(7/32 : ℝ))
    (_hd : (91/180 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(7/4 : ℝ) := h.xcap
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_44 {t d x : ℝ} (h : CornerRootData t d x)
    (_hl : (7/32 : ℝ)≤t) (hu : t≤(1/4 : ℝ))
    (_hd : (91/180 : ℝ)≤d) (he : d≤(377/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(7/4 : ℝ) := h.xcap
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_45 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/32 : ℝ)≤t) (hu : t≤(1/4 : ℝ))
    (hd : (377/720 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(413083/243000 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_46 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/32 : ℝ)≤t) (hu : t≤(1/4 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (377/720 : ℝ) with hm|hm
  · exact corner_grid_44 h hl hu hd hm
  · exact corner_grid_45 h hl hu hm.le he

private lemma corner_grid_47 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/16 : ℝ)≤t) (hu : t≤(1/4 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (7/32 : ℝ) with hm|hm
  · exact corner_grid_43 h hl hm hd he
  · exact corner_grid_46 h hm.le hu hd he

private lemma corner_grid_48 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/16 : ℝ)≤t) (hu : t≤(13/64 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(403/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(38272/22491 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_49 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (13/64 : ℝ)≤t) (hu : t≤(7/32 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(403/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(20416/12285 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_50 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/16 : ℝ)≤t) (hu : t≤(7/32 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(403/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (13/64 : ℝ) with hm|hm
  · exact corner_grid_48 h hl hm hd he
  · exact corner_grid_49 h hm.le hu hd he

private lemma corner_grid_51 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/16 : ℝ)≤t) (hu : t≤(13/64 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(91/160 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(487136/297675 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_52 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/16 : ℝ)≤t) (hu : t≤(13/64 : ℝ))
    (hd : (91/160 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(33384/20825 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_53 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/16 : ℝ)≤t) (hu : t≤(13/64 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (91/160 : ℝ) with hm|hm
  · exact corner_grid_51 h hl hu hd hm
  · exact corner_grid_52 h hl hu hm.le he

private lemma corner_grid_54 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (13/64 : ℝ)≤t) (hu : t≤(7/32 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(91/160 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(3151544/1974375 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_55 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (13/64 : ℝ)≤t) (hu : t≤(7/32 : ℝ))
    (hd : (91/160 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(266618/170625 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_56 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (13/64 : ℝ)≤t) (hu : t≤(7/32 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (91/160 : ℝ) with hm|hm
  · exact corner_grid_54 h hl hu hd hm
  · exact corner_grid_55 h hl hu hm.le he

private lemma corner_grid_57 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/16 : ℝ)≤t) (hu : t≤(7/32 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (13/64 : ℝ) with hm|hm
  · exact corner_grid_53 h hl hm hd he
  · exact corner_grid_56 h hm.le hu hd he

private lemma corner_grid_58 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/16 : ℝ)≤t) (hu : t≤(7/32 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (403/720 : ℝ) with hm|hm
  · exact corner_grid_50 h hl hu hd hm
  · exact corner_grid_57 h hl hu hm.le he

private lemma corner_grid_59 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/32 : ℝ)≤t) (hu : t≤(15/64 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(403/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(395648/243873 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_60 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (15/64 : ℝ)≤t) (hu : t≤(1/4 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(403/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(1496/945 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_61 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/32 : ℝ)≤t) (hu : t≤(1/4 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(403/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (15/64 : ℝ) with hm|hm
  · exact corner_grid_59 h hl hm hd he
  · exact corner_grid_60 h hm.le hu hd he

private lemma corner_grid_62 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/32 : ℝ)≤t) (hu : t≤(15/64 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(91/160 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(85392032/54871425 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_63 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/32 : ℝ)≤t) (hu : t≤(15/64 : ℝ))
    (hd : (91/160 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(1031272/677425 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_64 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/32 : ℝ)≤t) (hu : t≤(15/64 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (91/160 : ℝ) with hm|hm
  · exact corner_grid_62 h hl hu hd hm
  · exact corner_grid_63 h hl hu hm.le he

private lemma corner_grid_65 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (15/64 : ℝ)≤t) (hu : t≤(1/4 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(91/160 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(2579401/1701000 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_66 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (15/64 : ℝ)≤t) (hu : t≤(1/4 : ℝ))
    (hd : (91/160 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(5929/4000 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_67 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (15/64 : ℝ)≤t) (hu : t≤(1/4 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (91/160 : ℝ) with hm|hm
  · exact corner_grid_65 h hl hu hd hm
  · exact corner_grid_66 h hl hu hm.le he

private lemma corner_grid_68 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/32 : ℝ)≤t) (hu : t≤(1/4 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (15/64 : ℝ) with hm|hm
  · exact corner_grid_64 h hl hm hd he
  · exact corner_grid_67 h hm.le hu hd he

private lemma corner_grid_69 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/32 : ℝ)≤t) (hu : t≤(1/4 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (403/720 : ℝ) with hm|hm
  · exact corner_grid_61 h hl hu hd hm
  · exact corner_grid_68 h hl hu hm.le he

private lemma corner_grid_70 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/16 : ℝ)≤t) (hu : t≤(1/4 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (7/32 : ℝ) with hm|hm
  · exact corner_grid_58 h hl hm hd he
  · exact corner_grid_69 h hm.le hu hd he

private lemma corner_grid_71 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/16 : ℝ)≤t) (hu : t≤(1/4 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (13/24 : ℝ) with hm|hm
  · exact corner_grid_47 h hl hu hd hm
  · exact corner_grid_70 h hl hu hm.le he

private lemma corner_grid_72 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/8 : ℝ)≤t) (hu : t≤(1/4 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (3/16 : ℝ) with hm|hm
  · exact corner_grid_42 h hl hm hd he
  · exact corner_grid_71 h hm.le hu hd he

private lemma corner_grid_73 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/8 : ℝ)≤t) (hu : t≤(1/4 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (91/180 : ℝ) with hm|hm
  · exact corner_grid_3 h hl hu hd hm
  · exact corner_grid_72 h hl hu hm.le he

private lemma corner_grid_74 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (0/1 : ℝ)≤t) (hu : t≤(1/4 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (1/8 : ℝ) with hm|hm
  · exact corner_grid_2 h hl hm hd he
  · exact corner_grid_73 h hm.le hu hd he

lemma corner_grid_75 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (0/1 : ℝ)≤t) (hu : t≤(1/4 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (13/30 : ℝ) with hm|hm
  · exact corner_grid_1 h hl hu hd hm
  · exact corner_grid_74 h hl hu hm.le he

private lemma corner_grid_76 {t d x : ℝ} (h : CornerRootData t d x)
    (_hl : (1/4 : ℝ)≤t) (hu : t≤(3/8 : ℝ))
    (_hd : (13/45 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(7/4 : ℝ) := h.xcap
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_77 {t d x : ℝ} (h : CornerRootData t d x)
    (_hl : (3/8 : ℝ)≤t) (hu : t≤(1/2 : ℝ))
    (_hd : (13/45 : ℝ)≤d) (he : d≤(13/36 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(7/4 : ℝ) := h.xcap
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_78 {t d x : ℝ} (h : CornerRootData t d x)
    (_hl : (3/8 : ℝ)≤t) (hu : t≤(7/16 : ℝ))
    (_hd : (13/36 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(7/4 : ℝ) := h.xcap
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_79 {t d x : ℝ} (h : CornerRootData t d x)
    (_hl : (7/16 : ℝ)≤t) (hu : t≤(1/2 : ℝ))
    (_hd : (13/36 : ℝ)≤d) (he : d≤(143/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(7/4 : ℝ) := h.xcap
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_80 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/16 : ℝ)≤t) (hu : t≤(1/2 : ℝ))
    (hd : (143/360 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(82423/48600 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_81 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/16 : ℝ)≤t) (hu : t≤(1/2 : ℝ))
    (hd : (13/36 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (143/360 : ℝ) with hm|hm
  · exact corner_grid_79 h hl hu hd hm
  · exact corner_grid_80 h hl hu hm.le he

private lemma corner_grid_82 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/8 : ℝ)≤t) (hu : t≤(1/2 : ℝ))
    (hd : (13/36 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (7/16 : ℝ) with hm|hm
  · exact corner_grid_78 h hl hm hd he
  · exact corner_grid_81 h hm.le hu hd he

private lemma corner_grid_83 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/8 : ℝ)≤t) (hu : t≤(1/2 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (13/36 : ℝ) with hm|hm
  · exact corner_grid_77 h hl hu hd hm
  · exact corner_grid_82 h hl hu hm.le he

lemma corner_grid_84 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/4 : ℝ)≤t) (hu : t≤(1/2 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (3/8 : ℝ) with hm|hm
  · exact corner_grid_76 h hl hm hd he
  · exact corner_grid_83 h hm.le hu hd he

private lemma corner_grid_85 {t d x : ℝ} (h : CornerRootData t d x)
    (_hl : (1/4 : ℝ)≤t) (hu : t≤(5/16 : ℝ))
    (_hd : (13/30 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(7/4 : ℝ) := h.xcap
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_86 {t d x : ℝ} (h : CornerRootData t d x)
    (_hl : (5/16 : ℝ)≤t) (hu : t≤(3/8 : ℝ))
    (_hd : (13/30 : ℝ)≤d) (he : d≤(169/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(7/4 : ℝ) := h.xcap
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_87 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/16 : ℝ)≤t) (hu : t≤(11/32 : ℝ))
    (hd : (169/360 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(21309728/12800025 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_88 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/32 : ℝ)≤t) (hu : t≤(3/8 : ℝ))
    (hd : (169/360 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(112978/70875 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_89 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/16 : ℝ)≤t) (hu : t≤(3/8 : ℝ))
    (hd : (169/360 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (11/32 : ℝ) with hm|hm
  · exact corner_grid_87 h hl hm hd he
  · exact corner_grid_88 h hm.le hu hd he

private lemma corner_grid_90 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/16 : ℝ)≤t) (hu : t≤(3/8 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (169/360 : ℝ) with hm|hm
  · exact corner_grid_86 h hl hu hd hm
  · exact corner_grid_89 h hl hu hm.le he

private lemma corner_grid_91 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/4 : ℝ)≤t) (hu : t≤(3/8 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (5/16 : ℝ) with hm|hm
  · exact corner_grid_85 h hl hm hd he
  · exact corner_grid_90 h hm.le hu hd he

private lemma corner_grid_92 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/4 : ℝ)≤t) (hu : t≤(9/32 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(377/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(22554752/13367025 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_93 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/4 : ℝ)≤t) (hu : t≤(9/32 : ℝ))
    (hd : (377/720 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(21707048/13367025 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_94 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/4 : ℝ)≤t) (hu : t≤(9/32 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (377/720 : ℝ) with hm|hm
  · exact corner_grid_92 h hl hu hd hm
  · exact corner_grid_93 h hl hu hm.le he

private lemma corner_grid_95 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/32 : ℝ)≤t) (hu : t≤(5/16 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(377/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(480208/297675 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_96 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/32 : ℝ)≤t) (hu : t≤(5/16 : ℝ))
    (hd : (377/720 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(460942/297675 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_97 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/32 : ℝ)≤t) (hu : t≤(5/16 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (377/720 : ℝ) with hm|hm
  · exact corner_grid_95 h hl hu hd hm
  · exact corner_grid_96 h hl hu hm.le he

private lemma corner_grid_98 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/4 : ℝ)≤t) (hu : t≤(5/16 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (9/32 : ℝ) with hm|hm
  · exact corner_grid_94 h hl hm hd he
  · exact corner_grid_97 h hm.le hu hd he

private lemma corner_grid_99 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/4 : ℝ)≤t) (hu : t≤(17/64 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(403/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(370304/239841 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_100 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (17/64 : ℝ)≤t) (hu : t≤(9/32 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(403/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(89408/59409 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_101 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/4 : ℝ)≤t) (hu : t≤(9/32 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(403/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (17/64 : ℝ) with hm|hm
  · exact corner_grid_99 h hl hm hd he
  · exact corner_grid_100 h hm.le hu hd he

private lemma corner_grid_102 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/4 : ℝ)≤t) (hu : t≤(17/64 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(79689632/53964225 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_103 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (17/64 : ℝ)≤t) (hu : t≤(9/32 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(19209608/13367025 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_104 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/4 : ℝ)≤t) (hu : t≤(9/32 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (17/64 : ℝ) with hm|hm
  · exact corner_grid_102 h hl hm hd he
  · exact corner_grid_103 h hm.le hu hd he

private lemma corner_grid_105 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/4 : ℝ)≤t) (hu : t≤(9/32 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (403/720 : ℝ) with hm|hm
  · exact corner_grid_101 h hl hu hd hm
  · exact corner_grid_104 h hl hu hm.le he

private lemma corner_grid_106 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/32 : ℝ)≤t) (hu : t≤(19/64 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(403/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(9856/6723 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_107 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (19/64 : ℝ)≤t) (hu : t≤(5/16 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(403/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(1888/1323 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_108 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/32 : ℝ)≤t) (hu : t≤(5/16 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(403/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (19/64 : ℝ) with hm|hm
  · exact corner_grid_106 h hl hm hd he
  · exact corner_grid_107 h hm.le hu hd he

private lemma corner_grid_109 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/32 : ℝ)≤t) (hu : t≤(19/64 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(73987232/52943625 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_110 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (19/64 : ℝ)≤t) (hu : t≤(5/16 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(404182/297675 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_111 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/32 : ℝ)≤t) (hu : t≤(5/16 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (19/64 : ℝ) with hm|hm
  · exact corner_grid_109 h hl hm hd he
  · exact corner_grid_110 h hm.le hu hd he

private lemma corner_grid_112 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/32 : ℝ)≤t) (hu : t≤(5/16 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (403/720 : ℝ) with hm|hm
  · exact corner_grid_108 h hl hu hd hm
  · exact corner_grid_111 h hl hu hm.le he

private lemma corner_grid_113 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/4 : ℝ)≤t) (hu : t≤(5/16 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (9/32 : ℝ) with hm|hm
  · exact corner_grid_105 h hl hm hd he
  · exact corner_grid_112 h hm.le hu hd he

private lemma corner_grid_114 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/4 : ℝ)≤t) (hu : t≤(5/16 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (13/24 : ℝ) with hm|hm
  · exact corner_grid_98 h hl hu hd hm
  · exact corner_grid_113 h hl hu hm.le he

private lemma corner_grid_115 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/16 : ℝ)≤t) (hu : t≤(11/32 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(377/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(19703552/12800025 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_116 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/16 : ℝ)≤t) (hu : t≤(11/32 : ℝ))
    (hd : (377/720 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(18855848/12800025 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_117 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/16 : ℝ)≤t) (hu : t≤(11/32 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (377/720 : ℝ) with hm|hm
  · exact corner_grid_115 h hl hu hd hm
  · exact corner_grid_116 h hl hu hm.le he

private lemma corner_grid_118 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/32 : ℝ)≤t) (hu : t≤(3/8 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(377/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(14836/10125 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_119 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/32 : ℝ)≤t) (hu : t≤(3/8 : ℝ))
    (hd : (377/720 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(198071/141750 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_120 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/32 : ℝ)≤t) (hu : t≤(3/8 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (377/720 : ℝ) with hm|hm
  · exact corner_grid_118 h hl hu hd hm
  · exact corner_grid_119 h hl hu hm.le he

private lemma corner_grid_121 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/16 : ℝ)≤t) (hu : t≤(3/8 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (11/32 : ℝ) with hm|hm
  · exact corner_grid_117 h hl hm hd he
  · exact corner_grid_120 h hm.le hu hd he

private lemma corner_grid_122 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/16 : ℝ)≤t) (hu : t≤(21/64 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(403/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(319616/230265 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_123 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (21/64 : ℝ)≤t) (hu : t≤(11/32 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(403/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(76736/56889 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_124 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/16 : ℝ)≤t) (hu : t≤(11/32 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(403/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (21/64 : ℝ) with hm|hm
  · exact corner_grid_122 h hl hm hd he
  · exact corner_grid_123 h hm.le hu hd he

private lemma corner_grid_125 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/16 : ℝ)≤t) (hu : t≤(21/64 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(9754976/7401375 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_126 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (21/64 : ℝ)≤t) (hu : t≤(11/32 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(16358408/12800025 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_127 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/16 : ℝ)≤t) (hu : t≤(11/32 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (21/64 : ℝ) with hm|hm
  · exact corner_grid_125 h hl hm hd he
  · exact corner_grid_126 h hm.le hu hd he

private lemma corner_grid_128 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/16 : ℝ)≤t) (hu : t≤(11/32 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (403/720 : ℝ) with hm|hm
  · exact corner_grid_124 h hl hu hd hm
  · exact corner_grid_127 h hl hu hm.le he

private lemma corner_grid_129 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/32 : ℝ)≤t) (hu : t≤(23/64 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(403/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(294272/224721 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_130 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (23/64 : ℝ)≤t) (hu : t≤(3/8 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(403/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(80/63 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_131 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/32 : ℝ)≤t) (hu : t≤(3/8 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(403/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (23/64 : ℝ) with hm|hm
  · exact corner_grid_129 h hl hm hd he
  · exact corner_grid_130 h hm.le hu hd he

private lemma corner_grid_132 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/32 : ℝ)≤t) (hu : t≤(23/64 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(62582432/50562225 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_133 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (23/64 : ℝ)≤t) (hu : t≤(3/8 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(169691/141750 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_134 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/32 : ℝ)≤t) (hu : t≤(3/8 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (23/64 : ℝ) with hm|hm
  · exact corner_grid_132 h hl hm hd he
  · exact corner_grid_133 h hm.le hu hd he

private lemma corner_grid_135 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/32 : ℝ)≤t) (hu : t≤(3/8 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (403/720 : ℝ) with hm|hm
  · exact corner_grid_131 h hl hu hd hm
  · exact corner_grid_134 h hl hu hm.le he

private lemma corner_grid_136 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/16 : ℝ)≤t) (hu : t≤(3/8 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (11/32 : ℝ) with hm|hm
  · exact corner_grid_128 h hl hm hd he
  · exact corner_grid_135 h hm.le hu hd he

private lemma corner_grid_137 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/16 : ℝ)≤t) (hu : t≤(3/8 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (13/24 : ℝ) with hm|hm
  · exact corner_grid_121 h hl hu hd hm
  · exact corner_grid_136 h hl hu hm.le he

private lemma corner_grid_138 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/4 : ℝ)≤t) (hu : t≤(3/8 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (5/16 : ℝ) with hm|hm
  · exact corner_grid_114 h hl hm hd he
  · exact corner_grid_137 h hm.le hu hd he

lemma corner_grid_139 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/4 : ℝ)≤t) (hu : t≤(3/8 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (91/180 : ℝ) with hm|hm
  · exact corner_grid_91 h hl hu hd hm
  · exact corner_grid_138 h hl hu hm.le he

private lemma corner_grid_140 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/8 : ℝ)≤t) (hu : t≤(13/32 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(169/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(2216192/1346625 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_141 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (13/32 : ℝ)≤t) (hu : t≤(7/16 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(169/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(514448/326025 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_142 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/8 : ℝ)≤t) (hu : t≤(7/16 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(169/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (13/32 : ℝ) with hm|hm
  · exact corner_grid_140 h hl hm hd he
  · exact corner_grid_141 h hm.le hu hd he

private lemma corner_grid_143 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/8 : ℝ)≤t) (hu : t≤(13/32 : ℝ))
    (hd : (169/360 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(18458528/12119625 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_144 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (13/32 : ℝ)≤t) (hu : t≤(7/16 : ℝ))
    (hd : (169/360 : ℝ)≤d) (he : d≤(39/80 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(4258232/2934225 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_145 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (13/32 : ℝ)≤t) (hu : t≤(7/16 : ℝ))
    (hd : (39/80 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(50138/36225 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_146 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (13/32 : ℝ)≤t) (hu : t≤(7/16 : ℝ))
    (hd : (169/360 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (39/80 : ℝ) with hm|hm
  · exact corner_grid_144 h hl hu hd hm
  · exact corner_grid_145 h hl hu hm.le he

private lemma corner_grid_147 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/8 : ℝ)≤t) (hu : t≤(7/16 : ℝ))
    (hd : (169/360 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (13/32 : ℝ) with hm|hm
  · exact corner_grid_143 h hl hm hd he
  · exact corner_grid_146 h hm.le hu hd he

lemma corner_grid_148 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/8 : ℝ)≤t) (hu : t≤(7/16 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (169/360 : ℝ) with hm|hm
  · exact corner_grid_142 h hl hu hd hm
  · exact corner_grid_147 h hl hu hm.le he

private lemma corner_grid_149 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/16 : ℝ)≤t) (hu : t≤(15/32 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(169/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(1899392/1258425 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_150 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (15/32 : ℝ)≤t) (hu : t≤(1/2 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(169/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(27203/18900 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

lemma corner_grid_151 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/16 : ℝ)≤t) (hu : t≤(1/2 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(169/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (15/32 : ℝ) with hm|hm
  · exact corner_grid_149 h hl hm hd he
  · exact corner_grid_150 h hm.le hu hd he

private lemma corner_grid_152 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/16 : ℝ)≤t) (hu : t≤(15/32 : ℝ))
    (hd : (169/360 : ℝ)≤d) (he : d≤(39/80 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(15607328/11325825 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_153 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/16 : ℝ)≤t) (hu : t≤(15/32 : ℝ))
    (hd : (39/80 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(26136/19975 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

lemma corner_grid_154 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/16 : ℝ)≤t) (hu : t≤(15/32 : ℝ))
    (hd : (169/360 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (39/80 : ℝ) with hm|hm
  · exact corner_grid_152 h hl hu hd hm
  · exact corner_grid_153 h hl hu hm.le he

end CubicTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_CornerGrid155
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace CubicTorus

private lemma corner_grid_155 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (15/32 : ℝ)≤t) (hu : t≤(1/2 : ℝ))
    (hd : (169/360 : ℝ)≤d) (he : d≤(39/80 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(443179/340200 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_156 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (15/32 : ℝ)≤t) (hu : t≤(1/2 : ℝ))
    (hd : (39/80 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(20669/16800 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_157 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (15/32 : ℝ)≤t) (hu : t≤(1/2 : ℝ))
    (hd : (169/360 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (39/80 : ℝ) with hm|hm
  · exact corner_grid_155 h hl hu hd hm
  · exact corner_grid_156 h hl hu hm.le he

private lemma corner_grid_158 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/16 : ℝ)≤t) (hu : t≤(1/2 : ℝ))
    (hd : (169/360 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (15/32 : ℝ) with hm|hm
  · exact corner_grid_154 h hl hm hd he
  · exact corner_grid_157 h hm.le hu hd he

private lemma corner_grid_159 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/16 : ℝ)≤t) (hu : t≤(1/2 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (169/360 : ℝ) with hm|hm
  · exact corner_grid_151 h hl hu hd hm
  · exact corner_grid_158 h hl hu hm.le he

private lemma corner_grid_160 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/8 : ℝ)≤t) (hu : t≤(1/2 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (7/16 : ℝ) with hm|hm
  · exact corner_grid_148 h hl hm hd he
  · exact corner_grid_159 h hm.le hu hd he

private lemma corner_grid_161 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/8 : ℝ)≤t) (hu : t≤(13/32 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(377/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(16852352/12119625 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_162 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/8 : ℝ)≤t) (hu : t≤(13/32 : ℝ))
    (hd : (377/720 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(16004648/12119625 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_163 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/8 : ℝ)≤t) (hu : t≤(13/32 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (377/720 : ℝ) with hm|hm
  · exact corner_grid_161 h hl hu hd hm
  · exact corner_grid_162 h hl hu hm.le he

private lemma corner_grid_164 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (13/32 : ℝ)≤t) (hu : t≤(7/16 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(377/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(3856688/2934225 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_165 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (13/32 : ℝ)≤t) (hu : t≤(7/16 : ℝ))
    (hd : (377/720 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(3644762/2934225 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_166 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (13/32 : ℝ)≤t) (hu : t≤(7/16 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (377/720 : ℝ) with hm|hm
  · exact corner_grid_164 h hl hu hd hm
  · exact corner_grid_165 h hl hu hm.le he

private lemma corner_grid_167 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/8 : ℝ)≤t) (hu : t≤(7/16 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (13/32 : ℝ) with hm|hm
  · exact corner_grid_163 h hl hm hd he
  · exact corner_grid_166 h hm.le hu hd he

private lemma corner_grid_168 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/8 : ℝ)≤t) (hu : t≤(25/64 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(403/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(268928/218673 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_169 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (25/64 : ℝ)≤t) (hu : t≤(13/32 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(403/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(9152/7695 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_170 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/8 : ℝ)≤t) (hu : t≤(13/32 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(403/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (25/64 : ℝ) with hm|hm
  · exact corner_grid_168 h hl hm hd he
  · exact corner_grid_169 h hm.le hu hd he

private lemma corner_grid_171 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/8 : ℝ)≤t) (hu : t≤(25/64 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(56880032/49201425 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_172 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (25/64 : ℝ)≤t) (hu : t≤(13/32 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(13507208/12119625 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_173 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/8 : ℝ)≤t) (hu : t≤(13/32 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (25/64 : ℝ) with hm|hm
  · exact corner_grid_171 h hl hm hd he
  · exact corner_grid_172 h hm.le hu hd he

private lemma corner_grid_174 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/8 : ℝ)≤t) (hu : t≤(13/32 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (403/720 : ℝ) with hm|hm
  · exact corner_grid_170 h hl hu hd hm
  · exact corner_grid_173 h hl hu hm.le he

private lemma corner_grid_175 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (13/32 : ℝ)≤t) (hu : t≤(7/16 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(403/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(15224/13041 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_176 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (13/32 : ℝ)≤t) (hu : t≤(27/64 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(51177632/47727225 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_177 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (27/64 : ℝ)≤t) (hu : t≤(7/16 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(431486/419175 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_178 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (13/32 : ℝ)≤t) (hu : t≤(7/16 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (27/64 : ℝ) with hm|hm
  · exact corner_grid_176 h hl hm hd he
  · exact corner_grid_177 h hm.le hu hd he

private lemma corner_grid_179 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (13/32 : ℝ)≤t) (hu : t≤(7/16 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (403/720 : ℝ) with hm|hm
  · exact corner_grid_175 h hl hu hd hm
  · exact corner_grid_178 h hl hu hm.le he

private lemma corner_grid_180 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/8 : ℝ)≤t) (hu : t≤(7/16 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (13/32 : ℝ) with hm|hm
  · exact corner_grid_174 h hl hm hd he
  · exact corner_grid_179 h hm.le hu hd he

private lemma corner_grid_181 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/8 : ℝ)≤t) (hu : t≤(7/16 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (13/24 : ℝ) with hm|hm
  · exact corner_grid_167 h hl hu hd hm
  · exact corner_grid_180 h hl hu hm.le he

private lemma corner_grid_182 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/16 : ℝ)≤t) (hu : t≤(15/32 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(377/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(14001152/11325825 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_183 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/16 : ℝ)≤t) (hu : t≤(15/32 : ℝ))
    (hd : (377/720 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(1879064/1617975 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_184 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/16 : ℝ)≤t) (hu : t≤(15/32 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (377/720 : ℝ) with hm|hm
  · exact corner_grid_182 h hl hu hd hm
  · exact corner_grid_183 h hl hu hm.le he

private lemma corner_grid_185 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (15/32 : ℝ)≤t) (hu : t≤(1/2 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(377/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(196493/170100 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_186 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (15/32 : ℝ)≤t) (hu : t≤(1/2 : ℝ))
    (hd : (377/720 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(1465981/1360800 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_187 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (15/32 : ℝ)≤t) (hu : t≤(1/2 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (377/720 : ℝ) with hm|hm
  · exact corner_grid_185 h hl hu hd hm
  · exact corner_grid_186 h hl hu hm.le he

private lemma corner_grid_188 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/16 : ℝ)≤t) (hu : t≤(1/2 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (15/32 : ℝ) with hm|hm
  · exact corner_grid_184 h hl hm hd he
  · exact corner_grid_187 h hm.le hu hd he

private lemma corner_grid_189 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/16 : ℝ)≤t) (hu : t≤(15/32 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(403/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(54560/50337 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_190 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/16 : ℝ)≤t) (hu : t≤(15/32 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(11368808/11325825 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_191 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/16 : ℝ)≤t) (hu : t≤(15/32 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (403/720 : ℝ) with hm|hm
  · exact corner_grid_189 h hl hu hd hm
  · exact corner_grid_190 h hl hu hm.le he

private lemma corner_grid_192 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (15/32 : ℝ)≤t) (hu : t≤(1/2 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(403/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(1507/1512 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_193 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (15/32 : ℝ)≤t) (hu : t≤(1/2 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(1242901/1360800 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_194 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (15/32 : ℝ)≤t) (hu : t≤(1/2 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (403/720 : ℝ) with hm|hm
  · exact corner_grid_192 h hl hu hd hm
  · exact corner_grid_193 h hl hu hm.le he

private lemma corner_grid_195 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/16 : ℝ)≤t) (hu : t≤(1/2 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (15/32 : ℝ) with hm|hm
  · exact corner_grid_191 h hl hm hd he
  · exact corner_grid_194 h hm.le hu hd he

private lemma corner_grid_196 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/16 : ℝ)≤t) (hu : t≤(1/2 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (13/24 : ℝ) with hm|hm
  · exact corner_grid_188 h hl hu hd hm
  · exact corner_grid_195 h hl hu hm.le he

private lemma corner_grid_197 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/8 : ℝ)≤t) (hu : t≤(1/2 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (7/16 : ℝ) with hm|hm
  · exact corner_grid_181 h hl hm hd he
  · exact corner_grid_196 h hm.le hu hd he

private lemma corner_grid_198 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/8 : ℝ)≤t) (hu : t≤(1/2 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (91/180 : ℝ) with hm|hm
  · exact corner_grid_160 h hl hu hd hm
  · exact corner_grid_197 h hl hu hm.le he

private lemma corner_grid_199 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/4 : ℝ)≤t) (hu : t≤(1/2 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (3/8 : ℝ) with hm|hm
  · exact corner_grid_139 h hl hm hd he
  · exact corner_grid_198 h hm.le hu hd he

private lemma corner_grid_200 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/4 : ℝ)≤t) (hu : t≤(1/2 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (13/30 : ℝ) with hm|hm
  · exact corner_grid_84 h hl hu hd hm
  · exact corner_grid_199 h hl hu hm.le he

private lemma corner_grid_201 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (0/1 : ℝ)≤t) (hu : t≤(1/2 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (1/4 : ℝ) with hm|hm
  · exact corner_grid_75 h hl hm hd he
  · exact corner_grid_200 h hm.le hu hd he

lemma corner_grid_202_oai {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (0/1 : ℝ)≤t) (hu : t≤(1/2 : ℝ))
    (hd : (0/1 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (13/45 : ℝ) with hm|hm
  · exact corner_grid_0 h hl hu hd hm
  · exact corner_grid_201 h hl hu hm.le he

end CubicTorus
end
end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.corner_grid_202_oai := @OAI.CubicTorus.corner_grid_202_oai
