-- Prove2me | solution 1 for OAI.CubicTorus.corner_grid_269
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T17:20:19.772721+00:00
-- url     : https://prove2.me/submissions/e73c1aac-bd98-40b0-8363-3e639707e6ea

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

lemma corner_root_basic_bound {t d x : ℝ} (ht : t<1) (_hx : 0≤x)
    (he : Real.pi*(1-t-d^2)=x*(1-t^2)) : x*(1+t)≤Real.pi := by
  have hf : (Real.pi-x*(1+t))*(1-t)=Real.pi*d^2 := by nlinarith only [he]
  have hh : 0≤(Real.pi-x*(1+t))*(1-t) := hf ▸ mul_nonneg Real.pi_pos.le (sq_nonneg d)
  have := (mul_nonneg_iff_of_pos_right (show 0<1-t by linarith)).mp hh
  linarith

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

lemma corner_root_simple_bound {t d x l X : ℝ} (ht : t<1) (hx0 : 0≤x)
    (he : Real.pi*(1-t-d^2)=x*(1-t^2)) (hl : l≤t) (hl0 : -1<l)
    (hnum : (22/7 : ℝ)≤X*(1+l)) : x≤X := by
  have hb := corner_root_basic_bound ht hx0 he
  have ha := mul_nonneg hx0 (sub_nonneg.mpr hl)
  have hp : Real.pi<(22/7 : ℝ) := by linarith [Real.pi_lt_d4]
  exact (mul_le_mul_iff_left₀ (show 0<1+l by linarith)).mp (by nlinarith only [ha,hb,hnum,hp])

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
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_CornerGrid155
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace CubicTorus

lemma corner_grid_203 {t d x : ℝ} (h : CornerRootData t d x)
    (_hl : (1/2 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (_hd : (0/1 : ℝ)≤d) (he : d≤(13/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(7/4 : ℝ) := h.xcap
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_204 {t d x : ℝ} (h : CornerRootData t d x)
    (_hl : (3/4 : ℝ)≤t) (hu : t≤(1/1 : ℝ))
    (_hd : (0/1 : ℝ)≤d) (he : d≤(13/90 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(7/4 : ℝ) := h.xcap
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_205 {t d x : ℝ} (h : CornerRootData t d x)
    (_hl : (3/4 : ℝ)≤t) (hu : t≤(7/8 : ℝ))
    (_hd : (13/90 : ℝ)≤d) (he : d≤(13/60 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(7/4 : ℝ) := h.xcap
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_206 {t d x : ℝ} (h : CornerRootData t d x)
    (_hl : (3/4 : ℝ)≤t) (hu : t≤(13/16 : ℝ))
    (_hd : (13/60 : ℝ)≤d) (he : d≤(91/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(7/4 : ℝ) := h.xcap
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_207 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/4 : ℝ)≤t) (hu : t≤(25/32 : ℝ))
    (hd : (91/360 : ℝ)≤d) (he : d≤(13/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(8489888/5655825 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_208 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (25/32 : ℝ)≤t) (hu : t≤(13/16 : ℝ))
    (hd : (91/360 : ℝ)≤d) (he : d≤(13/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(252296/176175 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_209 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/4 : ℝ)≤t) (hu : t≤(13/16 : ℝ))
    (hd : (91/360 : ℝ)≤d) (he : d≤(13/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (25/32 : ℝ) with hm|hm
  · exact corner_grid_207 h hl hm hd he
  · exact corner_grid_208 h hm.le hu hd he

private lemma corner_grid_210 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/4 : ℝ)≤t) (hu : t≤(13/16 : ℝ))
    (hd : (13/60 : ℝ)≤d) (he : d≤(13/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (91/360 : ℝ) with hm|hm
  · exact corner_grid_206 h hl hu hd hm
  · exact corner_grid_209 h hl hu hm.le he

private lemma corner_grid_211 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (13/16 : ℝ)≤t) (hu : t≤(27/32 : ℝ))
    (hd : (13/60 : ℝ)≤d) (he : d≤(91/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(712448/464625 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_212 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (27/32 : ℝ)≤t) (hu : t≤(7/8 : ℝ))
    (hd : (13/60 : ℝ)≤d) (he : d≤(91/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(34628/23625 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_213 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (13/16 : ℝ)≤t) (hu : t≤(7/8 : ℝ))
    (hd : (13/60 : ℝ)≤d) (he : d≤(91/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (27/32 : ℝ) with hm|hm
  · exact corner_grid_211 h hl hm hd he
  · exact corner_grid_212 h hm.le hu hd he

private lemma corner_grid_214 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (13/16 : ℝ)≤t) (hu : t≤(27/32 : ℝ))
    (hd : (91/360 : ℝ)≤d) (he : d≤(13/48 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(5638688/4181625 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_215 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (13/16 : ℝ)≤t) (hu : t≤(27/32 : ℝ))
    (hd : (13/48 : ℝ)≤d) (he : d≤(13/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(23144/18585 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_216 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (13/16 : ℝ)≤t) (hu : t≤(27/32 : ℝ))
    (hd : (91/360 : ℝ)≤d) (he : d≤(13/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (13/48 : ℝ) with hm|hm
  · exact corner_grid_214 h hl hu hd hm
  · exact corner_grid_215 h hl hu hm.le he

private lemma corner_grid_217 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (27/32 : ℝ)≤t) (hu : t≤(7/8 : ℝ))
    (hd : (91/360 : ℝ)≤d) (he : d≤(13/48 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(263318/212625 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_218 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (27/32 : ℝ)≤t) (hu : t≤(7/8 : ℝ))
    (hd : (13/48 : ℝ)≤d) (he : d≤(13/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(2101/1890 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_219 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (27/32 : ℝ)≤t) (hu : t≤(7/8 : ℝ))
    (hd : (91/360 : ℝ)≤d) (he : d≤(13/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (13/48 : ℝ) with hm|hm
  · exact corner_grid_217 h hl hu hd hm
  · exact corner_grid_218 h hl hu hm.le he

private lemma corner_grid_220 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (13/16 : ℝ)≤t) (hu : t≤(7/8 : ℝ))
    (hd : (91/360 : ℝ)≤d) (he : d≤(13/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (27/32 : ℝ) with hm|hm
  · exact corner_grid_216 h hl hm hd he
  · exact corner_grid_219 h hm.le hu hd he

private lemma corner_grid_221 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (13/16 : ℝ)≤t) (hu : t≤(7/8 : ℝ))
    (hd : (13/60 : ℝ)≤d) (he : d≤(13/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (91/360 : ℝ) with hm|hm
  · exact corner_grid_213 h hl hu hd hm
  · exact corner_grid_220 h hl hu hm.le he

private lemma corner_grid_222 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/4 : ℝ)≤t) (hu : t≤(7/8 : ℝ))
    (hd : (13/60 : ℝ)≤d) (he : d≤(13/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (13/16 : ℝ) with hm|hm
  · exact corner_grid_210 h hl hm hd he
  · exact corner_grid_221 h hm.le hu hd he

private lemma corner_grid_223 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/4 : ℝ)≤t) (hu : t≤(7/8 : ℝ))
    (hd : (13/90 : ℝ)≤d) (he : d≤(13/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (13/60 : ℝ) with hm|hm
  · exact corner_grid_205 h hl hu hd hm
  · exact corner_grid_222 h hl hu hm.le he

private lemma corner_grid_224 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/8 : ℝ)≤t) (hu : t≤(15/16 : ℝ))
    (_hd : (13/90 : ℝ)≤d) (he : d≤(13/72 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(176/105 : ℝ) := corner_root_simple_bound h.t1 h.x0 h.root
    hl (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_225 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/8 : ℝ)≤t) (hu : t≤(29/32 : ℝ))
    (hd : (13/72 : ℝ)≤d) (he : d≤(13/60 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(168608/103761 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_226 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (29/32 : ℝ)≤t) (hu : t≤(15/16 : ℝ))
    (hd : (13/72 : ℝ)≤d) (he : d≤(143/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(27896/17577 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_227 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (29/32 : ℝ)≤t) (hu : t≤(15/16 : ℝ))
    (hd : (143/720 : ℝ)≤d) (he : d≤(13/60 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(619322/439425 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_228 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (29/32 : ℝ)≤t) (hu : t≤(15/16 : ℝ))
    (hd : (13/72 : ℝ)≤d) (he : d≤(13/60 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (143/720 : ℝ) with hm|hm
  · exact corner_grid_226 h hl hu hd hm
  · exact corner_grid_227 h hl hu hm.le he

private lemma corner_grid_229 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/8 : ℝ)≤t) (hu : t≤(15/16 : ℝ))
    (hd : (13/72 : ℝ)≤d) (he : d≤(13/60 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (29/32 : ℝ) with hm|hm
  · exact corner_grid_225 h hl hm hd he
  · exact corner_grid_228 h hm.le hu hd he

private lemma corner_grid_230 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/8 : ℝ)≤t) (hu : t≤(15/16 : ℝ))
    (hd : (13/90 : ℝ)≤d) (he : d≤(13/60 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (13/72 : ℝ) with hm|hm
  · exact corner_grid_224 h hl hu hd hm
  · exact corner_grid_229 h hl hu hm.le he

private lemma corner_grid_231 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (15/16 : ℝ)≤t) (hu : t≤(31/32 : ℝ))
    (_hd : (13/90 : ℝ)≤d) (he : d≤(13/72 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(352/217 : ℝ) := corner_root_simple_bound h.t1 h.x0 h.root
    hl (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_232 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (31/32 : ℝ)≤t) (hu : t≤(1/1 : ℝ))
    (_hd : (13/90 : ℝ)≤d) (he : d≤(13/80 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(704/441 : ℝ) := corner_root_simple_bound h.t1 h.x0 h.root
    hl (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_233 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (31/32 : ℝ)≤t) (hu : t≤(63/64 : ℝ))
    (hd : (13/80 : ℝ)≤d) (he : d≤(13/72 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(10912/22225 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_234 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (63/64 : ℝ)≤t) (_hu : t≤(1/1 : ℝ))
    (hd : (13/80 : ℝ)≤d) (_he : d≤(13/72 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  nlinarith only [h.dbound,h.d0,hd,hl]

private lemma corner_grid_235 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (31/32 : ℝ)≤t) (hu : t≤(1/1 : ℝ))
    (hd : (13/80 : ℝ)≤d) (he : d≤(13/72 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (63/64 : ℝ) with hm|hm
  · exact corner_grid_233 h hl hm hd he
  · exact corner_grid_234 h hm.le hu hd he

private lemma corner_grid_236 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (31/32 : ℝ)≤t) (hu : t≤(1/1 : ℝ))
    (hd : (13/90 : ℝ)≤d) (he : d≤(13/72 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (13/80 : ℝ) with hm|hm
  · exact corner_grid_232 h hl hu hd hm
  · exact corner_grid_235 h hl hu hm.le he

private lemma corner_grid_237 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (15/16 : ℝ)≤t) (hu : t≤(1/1 : ℝ))
    (hd : (13/90 : ℝ)≤d) (he : d≤(13/72 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (31/32 : ℝ) with hm|hm
  · exact corner_grid_231 h hl hm hd he
  · exact corner_grid_236 h hm.le hu hd he

private lemma corner_grid_238 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (15/16 : ℝ)≤t) (hu : t≤(61/64 : ℝ))
    (hd : (13/72 : ℝ)≤d) (he : d≤(143/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(43648/42525 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_239 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (61/64 : ℝ)≤t) (hu : t≤(31/32 : ℝ))
    (hd : (13/72 : ℝ)≤d) (he : d≤(143/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(26048/35721 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_240 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (15/16 : ℝ)≤t) (hu : t≤(31/32 : ℝ))
    (hd : (13/72 : ℝ)≤d) (he : d≤(143/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (61/64 : ℝ) with hm|hm
  · exact corner_grid_238 h hl hm hd he
  · exact corner_grid_239 h hm.le hu hd he

private lemma corner_grid_241 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (15/16 : ℝ)≤t) (hu : t≤(31/32 : ℝ))
    (hd : (143/720 : ℝ)≤d) (he : d≤(13/60 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(1051688/893025 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_242 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (15/16 : ℝ)≤t) (hu : t≤(31/32 : ℝ))
    (hd : (13/72 : ℝ)≤d) (he : d≤(13/60 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (143/720 : ℝ) with hm|hm
  · exact corner_grid_240 h hl hu hd hm
  · exact corner_grid_241 h hl hu hm.le he

private lemma corner_grid_243 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (31/32 : ℝ)≤t) (_hu : t≤(1/1 : ℝ))
    (hd : (13/72 : ℝ)≤d) (_he : d≤(13/60 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  nlinarith only [h.dbound,h.d0,hd,hl]

private lemma corner_grid_244 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (15/16 : ℝ)≤t) (hu : t≤(1/1 : ℝ))
    (hd : (13/72 : ℝ)≤d) (he : d≤(13/60 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (31/32 : ℝ) with hm|hm
  · exact corner_grid_242 h hl hm hd he
  · exact corner_grid_243 h hm.le hu hd he

private lemma corner_grid_245 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (15/16 : ℝ)≤t) (hu : t≤(1/1 : ℝ))
    (hd : (13/90 : ℝ)≤d) (he : d≤(13/60 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (13/72 : ℝ) with hm|hm
  · exact corner_grid_237 h hl hu hd hm
  · exact corner_grid_244 h hl hu hm.le he

private lemma corner_grid_246 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/8 : ℝ)≤t) (hu : t≤(1/1 : ℝ))
    (hd : (13/90 : ℝ)≤d) (he : d≤(13/60 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (15/16 : ℝ) with hm|hm
  · exact corner_grid_230 h hl hm hd he
  · exact corner_grid_245 h hm.le hu hd he

private lemma corner_grid_247 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/8 : ℝ)≤t) (hu : t≤(29/32 : ℝ))
    (hd : (13/60 : ℝ)≤d) (he : d≤(169/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(395648/288225 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_248 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/8 : ℝ)≤t) (hu : t≤(29/32 : ℝ))
    (hd : (169/720 : ℝ)≤d) (he : d≤(91/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(455576/370575 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_249 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/8 : ℝ)≤t) (hu : t≤(29/32 : ℝ))
    (hd : (13/60 : ℝ)≤d) (he : d≤(91/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (169/720 : ℝ) with hm|hm
  · exact corner_grid_247 h hl hu hd hm
  · exact corner_grid_248 h hl hu hm.le he

private lemma corner_grid_250 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (29/32 : ℝ)≤t) (hu : t≤(15/16 : ℝ))
    (hd : (13/60 : ℝ)≤d) (he : d≤(169/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(59312/48825 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_251 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (29/32 : ℝ)≤t) (hu : t≤(15/16 : ℝ))
    (hd : (169/720 : ℝ)≤d) (he : d≤(91/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(440858/439425 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_252 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (29/32 : ℝ)≤t) (hu : t≤(15/16 : ℝ))
    (hd : (13/60 : ℝ)≤d) (he : d≤(91/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (169/720 : ℝ) with hm|hm
  · exact corner_grid_250 h hl hu hd hm
  · exact corner_grid_251 h hl hu hm.le he

private lemma corner_grid_253 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/8 : ℝ)≤t) (hu : t≤(15/16 : ℝ))
    (hd : (13/60 : ℝ)≤d) (he : d≤(91/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (29/32 : ℝ) with hm|hm
  · exact corner_grid_249 h hl hm hd he
  · exact corner_grid_252 h hm.le hu hd he

private lemma corner_grid_254 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/8 : ℝ)≤t) (hu : t≤(29/32 : ℝ))
    (hd : (91/360 : ℝ)≤d) (he : d≤(13/48 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(2787488/2594025 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_255 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/8 : ℝ)≤t) (hu : t≤(29/32 : ℝ))
    (hd : (13/48 : ℝ)≤d) (he : d≤(13/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(1496/1647 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_256 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/8 : ℝ)≤t) (hu : t≤(29/32 : ℝ))
    (hd : (91/360 : ℝ)≤d) (he : d≤(13/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (13/48 : ℝ) with hm|hm
  · exact corner_grid_254 h hl hu hd hm
  · exact corner_grid_255 h hl hu hm.le he

private lemma corner_grid_257 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (29/32 : ℝ)≤t) (hu : t≤(15/16 : ℝ))
    (hd : (91/360 : ℝ)≤d) (he : d≤(13/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(340472/439425 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_258 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/8 : ℝ)≤t) (hu : t≤(15/16 : ℝ))
    (hd : (91/360 : ℝ)≤d) (he : d≤(13/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (29/32 : ℝ) with hm|hm
  · exact corner_grid_256 h hl hm hd he
  · exact corner_grid_257 h hm.le hu hd he

private lemma corner_grid_259 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/8 : ℝ)≤t) (hu : t≤(15/16 : ℝ))
    (hd : (13/60 : ℝ)≤d) (he : d≤(13/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (91/360 : ℝ) with hm|hm
  · exact corner_grid_253 h hl hu hd hm
  · exact corner_grid_258 h hl hu hm.le he

private lemma corner_grid_260 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (15/16 : ℝ)≤t) (hu : t≤(31/32 : ℝ))
    (hd : (13/60 : ℝ)≤d) (he : d≤(91/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(11264/14175 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_261 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (31/32 : ℝ)≤t) (_hu : t≤(1/1 : ℝ))
    (hd : (13/60 : ℝ)≤d) (_he : d≤(91/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  nlinarith only [h.dbound,h.d0,hd,hl]

private lemma corner_grid_262 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (15/16 : ℝ)≤t) (hu : t≤(1/1 : ℝ))
    (hd : (13/60 : ℝ)≤d) (he : d≤(91/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (31/32 : ℝ) with hm|hm
  · exact corner_grid_260 h hl hm hd he
  · exact corner_grid_261 h hm.le hu hd he

private lemma corner_grid_263 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (15/16 : ℝ)≤t) (_hu : t≤(1/1 : ℝ))
    (hd : (91/360 : ℝ)≤d) (_he : d≤(13/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  nlinarith only [h.dbound,h.d0,hd,hl]

private lemma corner_grid_264 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (15/16 : ℝ)≤t) (hu : t≤(1/1 : ℝ))
    (hd : (13/60 : ℝ)≤d) (he : d≤(13/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (91/360 : ℝ) with hm|hm
  · exact corner_grid_262 h hl hu hd hm
  · exact corner_grid_263 h hl hu hm.le he

private lemma corner_grid_265 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/8 : ℝ)≤t) (hu : t≤(1/1 : ℝ))
    (hd : (13/60 : ℝ)≤d) (he : d≤(13/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (15/16 : ℝ) with hm|hm
  · exact corner_grid_259 h hl hm hd he
  · exact corner_grid_264 h hm.le hu hd he

private lemma corner_grid_266 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/8 : ℝ)≤t) (hu : t≤(1/1 : ℝ))
    (hd : (13/90 : ℝ)≤d) (he : d≤(13/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (13/60 : ℝ) with hm|hm
  · exact corner_grid_246 h hl hu hd hm
  · exact corner_grid_265 h hl hu hm.le he

private lemma corner_grid_267 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/4 : ℝ)≤t) (hu : t≤(1/1 : ℝ))
    (hd : (13/90 : ℝ)≤d) (he : d≤(13/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (7/8 : ℝ) with hm|hm
  · exact corner_grid_223 h hl hm hd he
  · exact corner_grid_266 h hm.le hu hd he

lemma corner_grid_268 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/4 : ℝ)≤t) (hu : t≤(1/1 : ℝ))
    (hd : (0/1 : ℝ)≤d) (he : d≤(13/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (13/90 : ℝ) with hm|hm
  · exact corner_grid_204 h hl hu hd hm
  · exact corner_grid_267 h hl hu hm.le he

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

lemma corner_grid_269_oai {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/2 : ℝ)≤t) (hu : t≤(1/1 : ℝ))
    (hd : (0/1 : ℝ)≤d) (he : d≤(13/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (3/4 : ℝ) with hm|hm
  · exact corner_grid_203 h hl hm hd he
  · exact corner_grid_268 h hm.le hu hd he

end CubicTorus
end
end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.corner_grid_269_oai := @OAI.CubicTorus.corner_grid_269_oai
