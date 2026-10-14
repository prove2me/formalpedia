-- Prove2me | solution 1 for LogSobolevMC.TwoPoint.theorem_A_1
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-12T01:14:37.384152+00:00
-- url     : https://prove2.me/submissions/108d25ac-4cbb-466b-9bd4-122188ee844b

-- Complete checked reconstruction of the native sharp independent-refresh log-Sobolev theorem.
-- Licensed under Apache 2.0.
import Definitions.Def_LogSobolevMC_ChiSquare_Setting
import Definitions.Def_LogSobolevMC_TwoPoint_Setting
import Mathlib


-- Begin ScalarBasic

namespace LogSobolevMC.TwoPoint.Proof

noncomputable def coeff (p : ℝ) : ℝ :=
  if p = 1 / 2 then 2 else Real.log ((1-p)/p)/(1-2*p)

noncomputable def scalarEntropy (p x y : ℝ) : ℝ :=
  p*x^2*Real.log (x^2)+(1-p)*y^2*Real.log (y^2)-
    (p*x^2+(1-p)*y^2)*Real.log (p*x^2+(1-p)*y^2)

end LogSobolevMC.TwoPoint.Proof
-- End ScalarBasic

-- Begin ScalarDerivatives

namespace LogSobolevMC.TwoPoint.Proof

noncomputable def scalarH (p t : ℝ) : ℝ :=
  p*t^2*Real.log (t^2) - (p*t^2+1-p)*Real.log (p*t^2+1-p) -
    coeff p*p*(1-p)*(t-1)^2
noncomputable def scalarH₁ (p t : ℝ) : ℝ :=
  2*p*t*(Real.log (t^2)-Real.log (p*t^2+1-p)) - 2*coeff p*p*(1-p)*(t-1)
noncomputable def scalarH₂ (p t : ℝ) : ℝ :=
  2*p*(Real.log (t^2)-Real.log (p*t^2+1-p)) + 4*p*(1-p)/(p*t^2+1-p) -
    2*coeff p*p*(1-p)
noncomputable def scalarH₃ (p t : ℝ) : ℝ :=
  4*p*(1-p)*(1-p-p*t^2)/(t*(p*t^2+1-p)^2)

lemma scalar_mass_pos {p t : ℝ} (hp : 0 < p) (hp' : p < 1) : 0 < p*t^2+1-p := by
  nlinarith [mul_nonneg hp.le (sq_nonneg t)]

lemma scalarH_deriv {p t : ℝ} (hp : 0 < p) (hp' : p < 1) (ht : 0 < t) :
    HasDerivAt (scalarH p) (scalarH₁ p t) t := by
  have hm := scalar_mass_pos (t:=t) hp hp'
  have ht2 : t^2 ≠ 0 := pow_ne_zero 2 ht.ne'
  have hd := ((((hasDerivAt_id t).pow 2).const_mul p).add_const 1).sub_const p
  have h := ((((hasDerivAt_id t).pow 2).const_mul p).mul
      (((hasDerivAt_id t).pow 2).log ht2)).sub (hd.mul (hd.log (by simpa only [Pi.pow_apply, id_eq] using hm.ne')))
  have hh := h.sub ((((hasDerivAt_id t).sub_const 1).pow 2).const_mul (coeff p*p*(1-p)))
  convert hh using 1 <;> (try rfl); (try dsimp [scalarH,scalarH₁]);
    (try field_simp [ht.ne',hm.ne']); ring

lemma scalarH₁_deriv {p t : ℝ} (hp : 0 < p) (hp' : p < 1) (ht : 0 < t) :
    HasDerivAt (scalarH₁ p) (scalarH₂ p t) t := by
  have hm := scalar_mass_pos (t:=t) hp hp'
  have ht2 : t^2 ≠ 0 := pow_ne_zero 2 ht.ne'
  have hd := ((((hasDerivAt_id t).pow 2).const_mul p).add_const 1).sub_const p
  have hl := (((hasDerivAt_id t).pow 2).log ht2).sub
    (hd.log (by simpa only [Pi.pow_apply, id_eq] using hm.ne'))
  have hh := (((hasDerivAt_id t).const_mul (2*p)).mul hl).sub
    (((hasDerivAt_id t).sub_const 1).const_mul (2*coeff p*p*(1-p)))
  convert hh using 1 <;> (try rfl); (try dsimp [scalarH₁,scalarH₂]);
    (try field_simp [ht.ne',hm.ne']); ring

lemma scalarH₂_deriv {p t : ℝ} (hp : 0 < p) (hp' : p < 1) (ht : 0 < t) :
    HasDerivAt (scalarH₂ p) (scalarH₃ p t) t := by
  have hm := scalar_mass_pos (t:=t) hp hp'
  have ht2 : t^2 ≠ 0 := pow_ne_zero 2 ht.ne'
  have hd := ((((hasDerivAt_id t).pow 2).const_mul p).add_const 1).sub_const p
  have hl := (((hasDerivAt_id t).pow 2).log ht2).sub
    (hd.log (by simpa only [Pi.pow_apply, id_eq] using hm.ne'))
  have hh := ((hl.const_mul (2*p)).add ((hasDerivAt_const t (4*p*(1-p))).div hd
    (by simpa only [Pi.pow_apply, id_eq] using hm.ne'))).sub_const (2*coeff p*p*(1-p))
  convert hh using 1 <;> (try rfl); (try dsimp [scalarH₂,scalarH₃]);
    (try field_simp [ht.ne',hm.ne']); ring

end LogSobolevMC.TwoPoint.Proof
-- End ScalarDerivatives

-- Begin DerivativeOrder

open Set
namespace LogSobolevMC.TwoPoint.Proof

lemma derivative_mono_Icc {f g : ℝ → ℝ} {a b : ℝ}
    (hd : ∀ x ∈ Icc a b, HasDerivAt f (g x) x)
    (hg : ∀ x ∈ Icc a b, 0 ≤ g x) : MonotoneOn f (Icc a b) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
  · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
  · intro x hx
    exact (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [(hd x (interior_subset hx)).deriv]
    exact hg x (interior_subset hx)

lemma derivative_anti_Icc {f g : ℝ → ℝ} {a b : ℝ}
    (hd : ∀ x ∈ Icc a b, HasDerivAt f (g x) x)
    (hg : ∀ x ∈ Icc a b, g x ≤ 0) : AntitoneOn f (Icc a b) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc a b)
  · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
  · intro x hx
    exact (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [(hd x (interior_subset hx)).deriv]
    exact hg x (interior_subset hx)

lemma rolle_positive {f g : ℝ → ℝ} {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hd : ∀ x, 0 < x → HasDerivAt f (g x) x) (he : f a = f b) :
    ∃ c ∈ Ioo a b, g c = 0 := by
  apply exists_hasDerivAt_eq_zero hab
  · intro x hx
    exact (hd x (ha.trans_le hx.1)).continuousAt.continuousWithinAt
  · exact he
  · exact fun x hx => hd x (ha.trans hx.1)

end LogSobolevMC.TwoPoint.Proof
-- End DerivativeOrder

-- Begin CoefficientLog

open Set
namespace LogSobolevMC.TwoPoint.Proof

lemma log_ratio_bound {r : ℝ} (hr : 1 ≤ r) : 2 * Real.log r ≤ r - 1/r := by
  let f : ℝ → ℝ := fun x => x - 1/x - 2*Real.log x
  have hm : MonotoneOn f (Icc 1 r) := by
    apply derivative_mono_Icc (g:=fun x => (1-1/x)^2)
    · intro x hx
      have hxp : 0 < x := lt_of_lt_of_le zero_lt_one hx.1
      convert ((hasDerivAt_id x).sub ((hasDerivAt_const x 1).div
        (hasDerivAt_id x) hxp.ne')).sub ((Real.hasDerivAt_log hxp.ne').const_mul 2) using 1 <;> (try rfl);
        (try dsimp [f]); (try field_simp); ring
    · intro x _; positivity
  have hh := hm ⟨le_rfl,hr⟩ ⟨hr,le_rfl⟩ hr
  dsimp [f] at hh
  norm_num at hh
  simpa only [one_div] using hh

lemma two_mul_sub_le_log {r : ℝ} (hr : 1 ≤ r) : 2*(r-1) ≤ (r+1)*Real.log r := by
  let f : ℝ → ℝ := fun x => (x+1)*Real.log x - 2*(x-1)
  have hm : MonotoneOn f (Icc 1 r) := by
    apply derivative_mono_Icc (g:=fun x => Real.log x - 1 + 1/x)
    · intro x hx
      have hxp : 0 < x := lt_of_lt_of_le zero_lt_one hx.1
      convert (((hasDerivAt_id x).add_const 1).mul (Real.hasDerivAt_log hxp.ne')).sub
        (((hasDerivAt_id x).sub_const 1).const_mul 2) using 1 <;> (try rfl);
        (try dsimp [f]); (try field_simp); ring
    · intro x hx
      have hxp : 0 < x := lt_of_lt_of_le zero_lt_one hx.1
      have h := Real.one_sub_inv_le_log_of_pos hxp
      rw [one_div]
      linarith
  have hh := hm ⟨le_rfl,hr⟩ ⟨hr,le_rfl⟩ hr
  dsimp [f] at hh
  norm_num at hh
  linarith

noncomputable def ratioCoeff (r : ℝ) : ℝ := (r+1)*Real.log r/(r-1)

lemma ratioCoeff_ge_two {r : ℝ} (hr : 1 < r) : 2 ≤ ratioCoeff r := by
  apply (le_div_iff₀ (sub_pos.mpr hr)).mpr
  exact two_mul_sub_le_log hr.le

lemma ratioCoeff_mono : MonotoneOn ratioCoeff (Ioi 1) := by
  intro r hr s hs hrs
  have hd : ∀ x ∈ Icc r s, HasDerivAt ratioCoeff
      ((x - 1/x - 2*Real.log x)/(x-1)^2) x := by
    intro x hx
    have hxp : 0 < x := zero_lt_one.trans (hr.trans_le hx.1)
    have hxm : x-1 ≠ 0 := ne_of_gt (sub_pos.mpr (hr.trans_le hx.1))
    convert ((((hasDerivAt_id x).add_const 1).mul (Real.hasDerivAt_log hxp.ne')).div
      ((hasDerivAt_id x).sub_const 1) hxm) using 1 <;> (try rfl);
      (try dsimp [ratioCoeff]); (try field_simp); ring
  have hm := derivative_mono_Icc hd (fun x hx => div_nonneg
    (by have h := log_ratio_bound ((hr.trans_le hx.1).le); linarith) (sq_nonneg _))
  exact hm ⟨le_rfl,hrs⟩ ⟨hrs,le_rfl⟩ hrs

end LogSobolevMC.TwoPoint.Proof
-- End CoefficientLog

-- Begin ScalarCoefficient

namespace LogSobolevMC.TwoPoint.Proof

lemma ratio_gt_one {p : ℝ} (hp : 0 < p) (hp' : p < 1/2) : 1 < (1-p)/p := by
  apply (lt_div_iff₀ hp).mpr
  linarith

lemma coeff_eq_ratioCoeff {p : ℝ} (hp : 0 < p) (hp' : p < 1/2) :
    coeff p = ratioCoeff ((1-p)/p) := by
  unfold coeff ratioCoeff
  rw [if_neg (ne_of_lt hp')]
  have he : 1-2*p ≠ 0 := by linarith
  field_simp
  ring

lemma coeff_ge_two {p : ℝ} (hp : 0 < p) (hp' : p ≤ 1/2) : 2 ≤ coeff p := by
  rcases eq_or_lt_of_le hp' with he | he
  · simp [coeff,he]
  · rw [coeff_eq_ratioCoeff hp he]
    exact ratioCoeff_ge_two (ratio_gt_one hp he)

lemma coeff_pos {p : ℝ} (hp : 0 < p) (hp' : p ≤ 1/2) : 0 < coeff p := by
  linarith [coeff_ge_two hp hp']

lemma coeff_nonneg {p : ℝ} (hp : 0 < p) (hp' : p ≤ 1/2) : 0 ≤ coeff p :=
  (coeff_pos hp hp').le

lemma coeff_antitone {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) (hq : q ≤ 1/2) :
    coeff q ≤ coeff p := by
  rcases eq_or_lt_of_le hq with hq | hq
  · rw [hq]
    simpa [coeff] using coeff_ge_two hp (hpq.trans (le_of_eq hq))
  · have hp' := hpq.trans_lt hq
    have hqp := hp.trans_le hpq
    rw [coeff_eq_ratioCoeff hp hp',coeff_eq_ratioCoeff hqp hq]
    apply ratioCoeff_mono (ratio_gt_one hqp hq) (ratio_gt_one hp hp')
    apply (div_le_div_iff₀ hqp hp).mpr
    nlinarith

end LogSobolevMC.TwoPoint.Proof
-- End ScalarCoefficient

-- Begin ScalarZeros

namespace LogSobolevMC.TwoPoint.Proof

lemma scalarH_one (p : ℝ) : scalarH p 1 = 0 := by
  simp [scalarH]
lemma scalarH₁_one (p : ℝ) : scalarH₁ p 1 = 0 := by
  simp [scalarH₁]

lemma scalarH_ratio {p : ℝ} (hp : 0 < p) (hp' : p < 1/2) :
    scalarH p ((1-p)/p) = 0 ∧ scalarH₁ p ((1-p)/p) = 0 := by
  have hm : p*((1-p)/p)^2+1-p = (1-p)/p := by field_simp; ring_nf
  have hc : coeff p = Real.log ((1-p)/p)/(1-2*p) := by
    unfold coeff
    rw [if_neg (ne_of_lt hp')]
  have he : 1-2*p ≠ 0 := by linarith
  constructor
  · simp only [scalarH,hm,Real.log_pow,hc]
    generalize Real.log ((1-p)/p) = L
    field_simp [hp.ne',he]
    ring_nf
    field_simp [show 1-p*2 ≠ 0 by nlinarith]
    ring_nf
  · simp only [scalarH₁,hm,Real.log_pow,hc]
    generalize Real.log ((1-p)/p) = L
    field_simp [hp.ne',he]
    ring_nf

lemma scalarH_eq (p t : ℝ) :
    scalarH p t = scalarEntropy p t 1 - coeff p*p*(1-p)*(t-1)^2 := by
  simp [scalarH,scalarEntropy]
  ring_nf

lemma scalarEntropy_sharp {p : ℝ} (hp : 0 < p) (hp' : p < 1/2) :
    scalarEntropy p ((1-p)/p) 1 = coeff p*p*(1-p)*(((1-p)/p)-1)^2 := by
  have h := (scalarH_ratio hp hp').1
  rw [scalarH_eq] at h
  exact sub_eq_zero.mp h

end LogSobolevMC.TwoPoint.Proof
-- End ScalarZeros

-- Begin UnimodalRoots

open Set
namespace LogSobolevMC.TwoPoint.Proof

lemma unimodal_two_roots {g : ℝ → ℝ} {c u v : ℝ}
    (hi : StrictMonoOn g (Ioc 0 c)) (hd : StrictAntiOn g (Ici c))
    (hu : 0 < u) (huv : u < v) (hgu : g u = 0) (hgv : g v = 0) :
    u < c ∧ c < v ∧
    (∀ x, 0 < x → x ≤ u → g x ≤ 0) ∧
    (∀ x, u ≤ x → x ≤ v → 0 ≤ g x) ∧
    (∀ x, v ≤ x → g x ≤ 0) := by
  have huc : u < c := by
    by_contra h
    have hcu : c ≤ u := le_of_not_gt h
    have h := hd hcu (hcu.trans huv.le) huv
    rw [hgu,hgv] at h
    exact lt_irrefl 0 h
  have hcv : c < v := by
    by_contra h
    have hvc : v ≤ c := le_of_not_gt h
    have h := hi ⟨hu,huv.le.trans hvc⟩ ⟨hu.trans huv,hvc⟩ huv
    rw [hgu,hgv] at h
    exact lt_irrefl 0 h
  refine ⟨huc,hcv,?_,?_,?_⟩
  · intro x hx hxu
    simpa only [hgu] using hi.monotoneOn ⟨hx,hxu.trans huc.le⟩ ⟨hu,huc.le⟩ hxu
  · intro x hux hxv
    by_cases hxc : x ≤ c
    · simpa only [hgu] using hi.monotoneOn ⟨hu,huc.le⟩ ⟨hu.trans_le hux,hxc⟩ hux
    · simpa only [hgv] using hd.antitoneOn (le_of_not_ge hxc) hcv.le hxv
  · intro x hvx
    simpa only [hgv] using hd.antitoneOn hcv.le (hcv.le.trans hvx) hvx

end LogSobolevMC.TwoPoint.Proof
-- End UnimodalRoots

-- Begin DoubleZeroShape

open Set
namespace LogSobolevMC.TwoPoint.Proof

lemma derivative_three_roots_signs {f g : ℝ → ℝ} {a u e v b : ℝ}
    (ha : 0 < a) (hau : a < u) (hue : u < e) (hev : e < v) (hvb : v < b)
    (hd : ∀ x, 0 < x → HasDerivAt f (g x) x)
    (hga : ∀ x, 0 < x → x ≤ u → g x ≤ 0)
    (hgm : ∀ x, u ≤ x → x ≤ v → 0 ≤ g x)
    (hgb : ∀ x, v ≤ x → g x ≤ 0)
    (hfa : f a = 0) (hfe : f e = 0) (hfb : f b = 0) :
    (∀ x, 0 < x → x ≤ a → 0 ≤ f x) ∧
    (∀ x, a ≤ x → x ≤ e → f x ≤ 0) ∧
    (∀ x, e ≤ x → x ≤ b → 0 ≤ f x) ∧
    (∀ x, b ≤ x → f x ≤ 0) := by
  have hanti₁ (s t : ℝ) (hs : 0 < s) (htu : t ≤ u) : AntitoneOn f (Icc s t) :=
    derivative_anti_Icc (fun x hx => hd x (hs.trans_le hx.1))
      (fun x hx => hga x (hs.trans_le hx.1) (hx.2.trans htu))
  have hmono (s t : ℝ) (hus : u ≤ s) (htv : t ≤ v) : MonotoneOn f (Icc s t) :=
    derivative_mono_Icc (fun x hx => hd x (ha.trans (hau.trans_le (hus.trans hx.1))))
      (fun x hx => hgm x (hus.trans hx.1) (hx.2.trans htv))
  have hanti₂ (s t : ℝ) (hvs : v ≤ s) : AntitoneOn f (Icc s t) :=
    derivative_anti_Icc (fun x hx => hd x (ha.trans (hau.trans (hue.trans (hev.trans_le (hvs.trans hx.1))))))
      (fun x hx => hgb x (hvs.trans hx.1))
  refine ⟨?_,?_,?_,?_⟩
  · intro x hx hxa
    simpa only [hfa] using hanti₁ x a hx hau.le ⟨le_rfl,hxa⟩ ⟨hxa,le_rfl⟩ hxa
  · intro x hax hxe
    by_cases hxu : x ≤ u
    · simpa only [hfa] using hanti₁ a x ha hxu ⟨le_rfl,hax⟩ ⟨hax,le_rfl⟩ hax
    · have hux := (lt_of_not_ge hxu).le
      simpa only [hfe] using hmono x e hux hev.le ⟨le_rfl,hxe⟩ ⟨hxe,le_rfl⟩ hxe
  · intro x hex hxb
    by_cases hxv : x ≤ v
    · simpa only [hfe] using hmono e x hue.le hxv ⟨le_rfl,hex⟩ ⟨hex,le_rfl⟩ hex
    · have hvx := (lt_of_not_ge hxv).le
      simpa only [hfb] using hanti₂ x b hvx ⟨le_rfl,hxb⟩ ⟨hxb,le_rfl⟩ hxb
  · intro x hbx
    simpa only [hfb] using hanti₂ b x hvb.le ⟨le_rfl,hbx⟩ ⟨hbx,le_rfl⟩ hbx

lemma double_zero_unimodal_nonpos {f f₁ f₂ : ℝ → ℝ} {a b c : ℝ}
    (ha : 0 < a) (hab : a < b)
    (h₀ : ∀ x, 0 < x → HasDerivAt f (f₁ x) x)
    (h₁ : ∀ x, 0 < x → HasDerivAt f₁ (f₂ x) x)
    (hi : StrictMonoOn f₂ (Ioc 0 c)) (hd : StrictAntiOn f₂ (Ici c))
    (hfa : f a = 0) (hfb : f b = 0) (h₁a : f₁ a = 0) (h₁b : f₁ b = 0) :
    ∀ x, 0 < x → f x ≤ 0 := by
  obtain ⟨e,he,he₁⟩ := rolle_positive ha hab h₀ (hfa.trans hfb.symm)
  obtain ⟨u,hu,hu₂⟩ := rolle_positive ha he.1 h₁ (h₁a.trans he₁.symm)
  obtain ⟨v,hv,hv₂⟩ := rolle_positive (ha.trans he.1) he.2 h₁ (he₁.trans h₁b.symm)
  obtain ⟨_,_,hg₁,hg₂,hg₃⟩ := unimodal_two_roots hi hd (ha.trans hu.1)
    (hu.2.trans hv.1) hu₂ hv₂
  obtain ⟨hs₁,hs₂,hs₃,hs₄⟩ := derivative_three_roots_signs ha hu.1 hu.2 hv.1 hv.2
    h₁ hg₁ hg₂ hg₃ h₁a he₁ h₁b
  intro x hx
  by_cases hxa : x ≤ a
  · have hm : MonotoneOn f (Icc x a) := derivative_mono_Icc
      (fun y hy => h₀ y (hx.trans_le hy.1))
      (fun y hy => hs₁ y (hx.trans_le hy.1) hy.2)
    simpa only [hfa] using hm ⟨le_rfl,hxa⟩ ⟨hxa,le_rfl⟩ hxa
  have hax := (lt_of_not_ge hxa).le
  by_cases hxe : x ≤ e
  · have hm : AntitoneOn f (Icc a x) := derivative_anti_Icc
      (fun y hy => h₀ y (ha.trans_le hy.1))
      (fun y hy => hs₂ y hy.1 (hy.2.trans hxe))
    simpa only [hfa] using hm ⟨le_rfl,hax⟩ ⟨hax,le_rfl⟩ hax
  have hex := (lt_of_not_ge hxe).le
  by_cases hxb : x ≤ b
  · have hm : MonotoneOn f (Icc x b) := derivative_mono_Icc
      (fun y hy => h₀ y (hx.trans_le hy.1))
      (fun y hy => hs₃ y (hex.trans hy.1) hy.2)
    simpa only [hfb] using hm ⟨le_rfl,hxb⟩ ⟨hxb,le_rfl⟩ hxb
  have hbx := (lt_of_not_ge hxb).le
  have hm : AntitoneOn f (Icc b x) := derivative_anti_Icc
    (fun y hy => h₀ y ((ha.trans hab).trans_le hy.1))
    (fun y hy => hs₄ y hy.1)
  simpa only [hfb] using hm ⟨le_rfl,hbx⟩ ⟨hbx,le_rfl⟩ hbx

end LogSobolevMC.TwoPoint.Proof
-- End DoubleZeroShape

-- Begin ScalarShape

open Set
namespace LogSobolevMC.TwoPoint.Proof

lemma scalarH₂_shape {p : ℝ} (hp : 0 < p) (hp' : p < 1) :
    StrictMonoOn (scalarH₂ p) (Ioc 0 (Real.sqrt ((1-p)/p))) ∧
    StrictAntiOn (scalarH₂ p) (Ici (Real.sqrt ((1-p)/p))) := by
  let c := Real.sqrt ((1-p)/p)
  have hq : 0 < 1-p := sub_pos.mpr hp'
  have hc : 0 < c := Real.sqrt_pos.2 (div_pos hq hp)
  have hcs : p*c^2 = 1-p := by
    dsimp [c]
    rw [Real.sq_sqrt (div_pos hq hp).le]
    field_simp
  constructor
  · apply strictMonoOn_of_deriv_pos (convex_Ioc 0 c)
    · exact fun x hx => (scalarH₂_deriv hp hp' hx.1).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ioc] at hx
      rw [(scalarH₂_deriv hp hp' hx.1).deriv]
      have hh : 0 < 1-p-p*x^2 := by
        have hh := mul_pos hp (sub_pos.mpr ((sq_lt_sq₀ hx.1.le hc.le).2 hx.2))
        nlinarith only [hh,hcs]
      unfold scalarH₃
      exact div_pos (mul_pos (mul_pos (mul_pos (by norm_num) hp) hq) hh)
        (mul_pos hx.1 (sq_pos_of_pos (scalar_mass_pos hp hp')))
  · apply strictAntiOn_of_deriv_neg (convex_Ici c)
    · exact fun x hx => (scalarH₂_deriv hp hp' (hc.trans_le hx)).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hxp := hc.trans hx
      rw [(scalarH₂_deriv hp hp' hxp).deriv]
      have hh : 1-p-p*x^2 < 0 := by
        have hh := mul_pos hp (sub_pos.mpr ((sq_lt_sq₀ hc.le hxp.le).2 hx))
        nlinarith only [hh,hcs]
      unfold scalarH₃
      exact div_neg_of_neg_of_pos
        (mul_neg_of_pos_of_neg (mul_pos (mul_pos (by norm_num) hp) hq) hh)
        (mul_pos hxp (sq_pos_of_pos (scalar_mass_pos hp hp')))

lemma scalarH_nonpos_strict {p : ℝ} (hp : 0 < p) (hp' : p < 1/2) :
    ∀ t, 0 < t → scalarH p t ≤ 0 := by
  have hp1 : p < 1 := by linarith
  obtain ⟨hi,hd⟩ := scalarH₂_shape hp hp1
  obtain ⟨hz,hz₁⟩ := scalarH_ratio hp hp'
  exact double_zero_unimodal_nonpos zero_lt_one (ratio_gt_one hp hp')
    (fun t ht => scalarH_deriv hp hp1 ht) (fun t ht => scalarH₁_deriv hp hp1 ht)
    hi hd (scalarH_one p) hz (scalarH₁_one p) hz₁

lemma scalarH₂_half_nonpos {t : ℝ} (ht : 0 < t) : scalarH₂ (1/2) t ≤ 0 := by
  obtain ⟨hi,hd⟩ := scalarH₂_shape (p:=1/2) (by norm_num) (by norm_num)
  have he : Real.sqrt ((1-(1/2:ℝ))/(1/2)) = 1 := by norm_num
  rw [he] at hi hd
  have hz : scalarH₂ (1/2) 1 = 0 := by norm_num [scalarH₂,coeff]
  by_cases ht1 : t ≤ 1
  · simpa only [hz] using hi.monotoneOn ⟨ht,ht1⟩ ⟨zero_lt_one,le_rfl⟩ ht1
  · simpa only [hz] using hd.antitoneOn (by norm_num) (le_of_not_ge ht1) (le_of_not_ge ht1)

lemma scalarH_nonpos_half {t : ℝ} (ht : 0 < t) : scalarH (1/2) t ≤ 0 := by
  have h₁ : ∀ x, 0 < x → HasDerivAt (scalarH₁ (1/2)) (scalarH₂ (1/2) x) x :=
    fun x hx => scalarH₁_deriv (by norm_num) (by norm_num) hx
  have h₀ : ∀ x, 0 < x → HasDerivAt (scalarH (1/2)) (scalarH₁ (1/2) x) x :=
    fun x hx => scalarH_deriv (by norm_num) (by norm_num) hx
  by_cases ht1 : t ≤ 1
  · have hpos : ∀ x ∈ Icc t 1, 0 ≤ scalarH₁ (1/2) x := by
      intro x hx
      have hm := derivative_anti_Icc (a:=x) (b:=1) (fun y hy => h₁ y ((ht.trans_le hx.1).trans_le hy.1))
        (fun y hy => scalarH₂_half_nonpos ((ht.trans_le hx.1).trans_le hy.1))
      simpa only [scalarH₁_one] using hm ⟨le_rfl,hx.2⟩ ⟨hx.2,le_rfl⟩ hx.2
    have hm := derivative_mono_Icc (fun x hx => h₀ x (ht.trans_le hx.1)) hpos
    simpa only [scalarH_one] using hm ⟨le_rfl,ht1⟩ ⟨ht1,le_rfl⟩ ht1
  · have h1t := le_of_not_ge ht1
    have hneg : ∀ x ∈ Icc 1 t, scalarH₁ (1/2) x ≤ 0 := by
      intro x hx
      have hm := derivative_anti_Icc (a:=1) (b:=x) (fun y hy => h₁ y (zero_lt_one.trans_le hy.1))
        (fun y hy => scalarH₂_half_nonpos (zero_lt_one.trans_le hy.1))
      simpa only [scalarH₁_one] using hm ⟨le_rfl,hx.1⟩ ⟨hx.1,le_rfl⟩ hx.1
    have hm := derivative_anti_Icc (fun x hx => h₀ x (zero_lt_one.trans_le hx.1)) hneg
    simpa only [scalarH_one] using hm ⟨le_rfl,h1t⟩ ⟨h1t,le_rfl⟩ h1t

end LogSobolevMC.TwoPoint.Proof
-- End ScalarShape

-- Begin SquareLog

open Filter Topology
namespace LogSobolevMC.TwoPoint.Proof

noncomputable def squareLog (x : ℝ) : ℝ := x^2 * Real.log (x^2)

lemma continuous_squareLog : Continuous squareLog :=
  Real.continuous_mul_log.comp (continuous_pow 2)

lemma squareLog_abs (x : ℝ) : squareLog |x| = squareLog x := by simp [squareLog]
lemma squareLog_zero : squareLog 0 = 0 := by simp [squareLog]

lemma squareLog_deriv (x : ℝ) :
    HasDerivAt squareLog (2*x*(Real.log (x^2)+1)) x := by
  by_cases hx : x=0
  · subst x
    simp only [mul_zero, zero_mul]
    rw [hasDerivAt_iff_tendsto_slope_zero]
    have he : (fun t : ℝ => t⁻¹ * (squareLog (0+t)-squareLog 0)) =
        fun t => 2*(t*Real.log t) := by
      funext t
      simp only [zero_add, squareLog, zero_pow (by decide : 2≠0), zero_mul, sub_zero,
        Real.log_pow]
      by_cases ht : t=0
      · simp [ht]
      · field_simp
        ; ring
    simp only [smul_eq_mul]
    rw [he]
    have h := (Real.continuous_mul_log.const_mul 2).continuousAt (x := 0)
    simpa using h.tendsto.mono_left nhdsWithin_le_nhds
  · have hp : HasDerivAt (fun t : ℝ => t^2) (2*x) x := by
      simpa using (hasDerivAt_pow 2 x)
    have h := (Real.hasDerivAt_mul_log (pow_ne_zero 2 hx)).comp (h := fun t : ℝ => t^2) x hp
    rw [show (Real.log (x^2)+1)*(2*x)=2*x*(Real.log (x^2)+1) by ring] at h
    exact h

lemma squareLog_smul (c x : ℝ) :
    squareLog (c*x) = c^2*squareLog x + c^2*x^2*Real.log (c^2) := by
  by_cases hc : c=0
  · simp [hc, squareLog]
  by_cases hx : x=0
  · simp [hx, squareLog]
  simp only [squareLog, mul_pow, Real.log_mul (pow_ne_zero 2 hc) (pow_ne_zero 2 hx)]
  ring

end LogSobolevMC.TwoPoint.Proof
-- End SquareLog

-- Begin ScalarScaling

namespace LogSobolevMC.TwoPoint.Proof

lemma mul_log_mul (a b : ℝ) :
    (a*b)*Real.log (a*b) = a*b*Real.log a + a*b*Real.log b := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  rw [Real.log_mul ha hb]
  ring

lemma scalarEntropy_scale (p c x y : ℝ) :
    scalarEntropy p (c*x) (c*y) = c^2*scalarEntropy p x y := by
  have heq (a b : ℝ) : scalarEntropy p a b = p*squareLog a+(1-p)*squareLog b-
      (p*a^2+(1-p)*b^2)*Real.log (p*a^2+(1-p)*b^2) := by
    dsimp [scalarEntropy,squareLog]
    ring
  rw [heq]
  have he : p*(c*x)^2+(1-p)*(c*y)^2 = c^2*(p*x^2+(1-p)*y^2) := by ring
  rw [squareLog_smul,squareLog_smul,he,mul_log_mul]
  dsimp [squareLog,scalarEntropy]
  ring

lemma continuous_scalarEntropy (p : ℝ) :
    Continuous (fun z : ℝ × ℝ => scalarEntropy p z.1 z.2) := by
  have hx := continuous_squareLog.comp (continuous_fst : Continuous (fun z : ℝ × ℝ => z.1))
  have hy := continuous_squareLog.comp (continuous_snd : Continuous (fun z : ℝ × ℝ => z.2))
  have hm : Continuous (fun z : ℝ × ℝ => p*z.1^2+(1-p)*z.2^2) := by fun_prop
  have hh := Real.continuous_mul_log.comp hm
  convert (hx.const_mul p).add (hy.const_mul (1-p)) |>.sub hh using 1
  ext z
  dsimp [squareLog,scalarEntropy]
  ring

end LogSobolevMC.TwoPoint.Proof
-- End ScalarScaling

-- Begin ScalarSharp

open Set Filter
open scoped Topology
namespace LogSobolevMC.TwoPoint.Proof

lemma scalarEntropy_le_positive {p x y : ℝ} (hp : 0 < p) (hp' : p ≤ 1/2)
    (hx : 0 < x) (hy : 0 < y) :
    scalarEntropy p x y ≤ coeff p*p*(1-p)*(x-y)^2 := by
  have hh : scalarH p (x/y) ≤ 0 := by
    rcases eq_or_lt_of_le hp' with he | he
    · rw [he]
      exact scalarH_nonpos_half (div_pos hx hy)
    · exact scalarH_nonpos_strict hp he (x/y) (div_pos hx hy)
  rw [scalarH_eq] at hh
  have h := mul_le_mul_of_nonneg_left (sub_nonpos.mp hh) (sq_nonneg y)
  have he := scalarEntropy_scale p y (x/y) 1
  have hxy : y*(x/y)=x := by field_simp
  rw [hxy,mul_one] at he
  rw [←he] at h
  convert h using 1 <;> (try rfl)
  field_simp

lemma scalarEntropy_le {p x y : ℝ} (hp : 0 < p) (hp' : p ≤ 1/2)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    scalarEntropy p x y ≤ coeff p*p*(1-p)*(x-y)^2 := by
  have hpair : Continuous (fun t : ℝ => (x+t,y+t)) := by fun_prop
  have hc : Continuous (fun t : ℝ => scalarEntropy p (x+t) (y+t)) :=
    (continuous_scalarEntropy p).comp hpair
  have ht : Tendsto (fun t : ℝ => scalarEntropy p (x+t) (y+t)) (𝓝[>] (0:ℝ))
      (𝓝 (scalarEntropy p x y)) := by
    simpa using (hc.continuousAt (x:=0)).tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0 < t at ht
  have h := scalarEntropy_le_positive hp hp' (by linarith : 0 < x+t) (by linarith : 0 < y+t)
  simpa only [add_sub_add_right_eq_sub] using h

end LogSobolevMC.TwoPoint.Proof
-- End ScalarSharp

-- Begin WeightedBasic

open scoped BigOperators
namespace LogSobolevMC.ChiSquare.Proof

variable {V : Type*} [Fintype V]

def mean (π f : V → ℝ) : ℝ := ∑ x, π x * f x

def squareMean (π f : V → ℝ) : ℝ := ∑ x, π x * (f x)^2

theorem squareMean_nonneg {π : V → ℝ} (hπ : ∀ x, 0 ≤ π x) (f : V → ℝ) :
    0 ≤ squareMean π f :=
  Finset.sum_nonneg fun x _ => mul_nonneg (hπ x) (sq_nonneg _)

theorem mean_const {π : V → ℝ} (hπ : ∑ x, π x = 1) (c : ℝ) :
    mean π (fun _ => c) = c := by
  simp only [mean, ← Finset.sum_mul, hπ, one_mul]

theorem mean_sub (π f g : V → ℝ) :
    mean π (fun x => f x-g x) = mean π f-mean π g := by
  simp only [mean, mul_sub, Finset.sum_sub_distrib]

theorem mean_smul (π f : V → ℝ) (c : ℝ) :
    mean π (fun x => c*f x) = c*mean π f := by
  simp only [mean, Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; ring

theorem squareMean_smul (π f : V → ℝ) (c : ℝ) :
    squareMean π (fun x => c*f x) = c^2*squareMean π f := by
  simp only [squareMean, Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; ring

theorem variance_eq_squareMean {π : V → ℝ} (hπ : ∑ x, π x = 1) (f : V → ℝ) :
    MarkovMixing.distVar π f = squareMean π f - (mean π f)^2 := by
  have hm : MarkovMixing.distExp π f = mean π f := by
    simp only [MarkovMixing.distExp, mean, mul_comm]
  rw [MarkovMixing.distVar, hm]
  calc
    _ = ∑ x, (π x*(f x)^2 - 2*mean π f*(π x*f x) + (mean π f)^2*π x) := by
      apply Finset.sum_congr rfl; intro x _; ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        hπ, mul_one]
      unfold mean squareMean; ring

theorem squareMean_eq_zero_iff {π : V → ℝ} (hπ : ∀ x, 0 < π x) (f : V → ℝ) :
    squareMean π f = 0 ↔ ∀ x, f x=0 := by
  constructor
  · intro h x
    have hx : π x*(f x)^2 ≤ squareMean π f :=
      Finset.single_le_sum (fun y _ => mul_nonneg (hπ y).le (sq_nonneg _)) (Finset.mem_univ x)
    rw [h] at hx
    have : (f x)^2 ≤ 0 := by nlinarith [hπ x]
    nlinarith [sq_nonneg (f x)]
  · intro h; simp [squareMean,h]

end LogSobolevMC.ChiSquare.Proof
-- End WeightedBasic

-- Begin EntropyBasic

open scoped BigOperators
namespace LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V]

theorem log_term_lower {a m : ℝ} (ha : 0 ≤ a) (hm : 0 < m) :
    a-m ≤ a*Real.log (a/m) := by
  by_cases h : a=0
  · subst a; simp; exact hm.le
  have ha' : 0<a := lt_of_le_of_ne ha (Ne.symm h)
  have hl := Real.log_le_sub_one_of_pos (div_pos hm ha')
  have he : Real.log (m/a) = -Real.log (a/m) := by
    rw [Real.log_div hm.ne' ha'.ne', Real.log_div ha'.ne' hm.ne']; ring
  rw [he] at hl
  have hh := mul_le_mul_of_nonneg_left hl ha
  have he' : a*(m/a-1)=m-a := by field_simp
  rw [he'] at hh; linarith

theorem log_term_upper {a m : ℝ} (ha : 0 ≤ a) (hm : 0 < m) :
    a*Real.log (a/m) ≤ a^2/m-a := by
  by_cases h : a=0
  · subst a; simp
  have ha' : 0<a := lt_of_le_of_ne ha (Ne.symm h)
  have hh := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos ha' hm)) ha
  calc
    _ ≤ a*(a/m-1) := hh
    _ = _ := by ring

theorem lpNorm_two_sq {π : V → ℝ} (hπ : ∀ x, 0 ≤ π x) (f : V → ℝ) :
    (lpNorm π 2 f)^2 = squareMean π f := by
  have hs : (∑ x, |f x|^(2:ℝ)*π x) = squareMean π f := by
    simp only [Real.rpow_two, sq_abs, squareMean, mul_comm]
  unfold lpNorm
  rw [hs, ← Real.sqrt_eq_rpow, Real.sq_sqrt (squareMean_nonneg hπ f)]

theorem entL_eq {π : V → ℝ} (hπ : ∀ x, 0 ≤ π x) (f : V → ℝ) :
    entL π f = ∑ x, π x*(f x)^2*Real.log ((f x)^2/squareMean π f) := by
  simp only [entL, Real.rpow_two, sq_abs, lpNorm_two_sq hπ]
  apply Finset.sum_congr rfl; intro x _; ring

theorem entL_nonneg_dist {π : V → ℝ} (hπ : MarkovMixing.IsDist π)
    (hpos : ∀ x, 0 < π x) (f : V → ℝ) : 0 ≤ entL π f := by
  rw [entL_eq hπ.1]
  by_cases hm : squareMean π f=0
  · have hf := (squareMean_eq_zero_iff hpos f).mp hm
    simp [hf]
  have hm' := lt_of_le_of_ne (squareMean_nonneg hπ.1 f) (Ne.symm hm)
  have h := Finset.sum_le_sum (s := Finset.univ) (fun x _ =>
    mul_le_mul_of_nonneg_left (log_term_lower (sq_nonneg (f x)) hm') (hπ.1 x))
  have he : (∑ x, π x*((f x)^2-squareMean π f)) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hπ.2, one_mul]
    change squareMean π f-squareMean π f=0; ring
  rw [he] at h
  simpa only [mul_assoc] using h

theorem entL_nonneg {K : Matrix V V ℝ} {π : V → ℝ}
    (hπ : MarkovMixing.IsStationary K π) (hpos : ∀ x, 0 < π x) (f : V → ℝ) :
    0 ≤ entL π f := entL_nonneg_dist hπ.1 hpos f

end LogSobolevMC.ChiSquare.Proof
-- End EntropyBasic

-- Begin EntropyModel

open scoped BigOperators
namespace LogSobolevMC.TwoPoint.Proof
open LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V]

noncomputable def entropy (π f : V → ℝ) : ℝ :=
  (∑ i, π i * squareLog (f i)) - squareMean π f * Real.log (squareMean π f)

noncomputable def deficit (π : V → ℝ) (C : ℝ) (f : V → ℝ) : ℝ :=
  C*(squareMean π f-(mean π f)^2)-entropy π f

lemma continuous_mean (π : V → ℝ) : Continuous (mean π) := by
  unfold mean
  fun_prop
lemma continuous_squareMean (π : V → ℝ) : Continuous (squareMean π) := by
  unfold squareMean
  fun_prop
lemma continuous_entropy (π : V → ℝ) : Continuous (entropy π) := by
  apply Continuous.sub
  · apply continuous_finsetSum
    intro i _
    exact continuous_const.mul (continuous_squareLog.comp (continuous_apply i))
  · exact Real.continuous_mul_log.comp (continuous_squareMean π)
lemma continuous_deficit (π : V → ℝ) (C : ℝ) : Continuous (deficit π C) :=
  continuous_const.mul ((continuous_squareMean π).sub ((continuous_mean π).pow 2)) |>.sub
    (continuous_entropy π)

lemma entropy_native {π : V → ℝ} (hπ : ∀ i, 0 < π i) (f : V → ℝ) :
    entropy π f = LogSobolevMC.ChiSquare.entL π f := by
  rw [entL_eq (fun i => (hπ i).le)]
  by_cases hS : squareMean π f=0
  · have hf := (squareMean_eq_zero_iff hπ f).mp hS
    simp [entropy,hf,squareLog,hS]
  unfold entropy
  have he (i : V) : π i*squareLog (f i) - π i*(f i)^2*Real.log (squareMean π f) =
      π i*(f i)^2*Real.log ((f i)^2/squareMean π f) := by
    by_cases hf : f i=0
    · simp [hf,squareLog]
    · rw [Real.log_div (pow_ne_zero 2 hf) hS]
      unfold squareLog
      ring
  rw [show squareMean π f*Real.log (squareMean π f)=
      ∑ i, π i*(f i)^2*Real.log (squareMean π f) by rw [←Finset.sum_mul]; rfl,
    ←Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun i _ => he i)

lemma entropy_smul (π f : V → ℝ) (c : ℝ) :
    entropy π (fun i => c*f i) = c^2*entropy π f := by
  by_cases hc : c=0
  · simp [entropy,squareLog,squareMean,hc]
  by_cases hS : squareMean π f=0
  · simp only [entropy,squareMean_smul,hS,mul_zero,zero_mul,sub_zero,squareLog_smul,
      mul_add,Finset.sum_add_distrib]
    have he : (∑ i, π i*(c^2*(f i)^2*Real.log (c^2)))=0 := by
      calc
        _ = c^2*Real.log (c^2)*squareMean π f := by
          simp only [squareMean,Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = 0 := by rw [hS,mul_zero]
    rw [he,add_zero]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · simp only [entropy,squareMean_smul,squareLog_smul,
      Real.log_mul (pow_ne_zero 2 hc) hS,mul_add,Finset.sum_add_distrib]
    have he : (∑ i, π i*(c^2*(f i)^2*Real.log (c^2))) =
        c^2*squareMean π f*Real.log (c^2) := by
      simp only [squareMean,Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he]
    have he' : (∑ i, π i*(c^2*squareLog (f i)))=c^2*∑ i,π i*squareLog (f i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he']
    ring

lemma deficit_smul (π f : V → ℝ) (C c : ℝ) :
    deficit π C (fun i => c*f i)=c^2*deficit π C f := by
  rw [deficit,deficit,squareMean_smul,mean_smul,entropy_smul]
  ring

end LogSobolevMC.TwoPoint.Proof
-- End EntropyModel

-- Begin DeficitCompact

open scoped BigOperators
namespace LogSobolevMC.TwoPoint.Proof
open LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V]

lemma squareMean_abs (π f : V → ℝ) : squareMean π (fun i => |f i|)=squareMean π f := by
  simp only [squareMean,sq_abs]
lemma entropy_abs (π f : V → ℝ) : entropy π (fun i => |f i|)=entropy π f := by
  simp only [entropy,squareLog_abs,squareMean_abs]
lemma abs_mean_le {π : V → ℝ} (hπ : ∀ i, 0 ≤ π i) (f : V → ℝ) :
    |mean π f| ≤ mean π (fun i => |f i|) := by
  simpa only [mean,abs_mul,abs_of_nonneg (hπ _)] using
    (Finset.abs_sum_le_sum_abs (s := Finset.univ) (f := fun i => π i*f i))
lemma deficit_abs_le {π : V → ℝ} (hπ : ∀ i, 0 ≤ π i) (f : V → ℝ)
    {C : ℝ} (hC : 0 ≤ C) : deficit π C (fun i => |f i|) ≤ deficit π C f := by
  have hm := abs_mean_le hπ f
  have ha : 0 ≤ mean π (fun i => |f i|) :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hπ i) (abs_nonneg _))
  have hsq : (mean π f)^2 ≤ (mean π (fun i => |f i|))^2 :=
    (sq_le_sq).mpr (by rwa [abs_of_nonneg ha])
  unfold deficit
  rw [squareMean_abs,entropy_abs]
  exact sub_le_sub_right (mul_le_mul_of_nonneg_left (sub_le_sub_left hsq _) hC) _

lemma unitSphere_compact {π : V → ℝ} (hπ : ∀ i, 0 < π i) :
    IsCompact {f : V → ℝ | squareMean π f=1} := by
  have hc : IsClosed {f : V → ℝ | squareMean π f=1} :=
    isClosed_eq (continuous_squareMean π) continuous_const
  apply (isCompact_Icc : IsCompact (Set.Icc (fun i => -(1+1/π i)) (fun i => 1+1/π i))).of_isClosed_subset hc
  intro f hf
  have hb (i : V) : (f i)^2 ≤ 1/π i := by
    apply (le_div_iff₀ (hπ i)).mpr
    have h := Finset.single_le_sum (fun j _ => mul_nonneg (hπ j).le (sq_nonneg (f j)))
      (Finset.mem_univ i)
    change π i*(f i)^2 ≤ squareMean π f at h
    rw [hf] at h
    nlinarith only [h]
  constructor <;> intro i <;>
    nlinarith [hb i, sq_nonneg (f i-1),sq_nonneg (f i+1),one_div_pos.mpr (hπ i)]

lemma deficit_minimizer {π : V → ℝ} (hπ : MarkovMixing.IsDist π)
    (hpos : ∀ i, 0 < π i) {C : ℝ} (hC : 0 ≤ C) :
    ∃ f : V → ℝ, (∀ i, 0 ≤ f i) ∧ squareMean π f=1 ∧
      ∀ g, squareMean π g=1 → deficit π C f ≤ deficit π C g := by
  have hn : ({f : V → ℝ | squareMean π f=1} : Set (V → ℝ)).Nonempty := by
    refine ⟨fun _ => 1, ?_⟩
    change squareMean π (fun _ => 1)=1
    simpa only [squareMean,one_pow,mul_one] using hπ.2
  obtain ⟨f,hf,hmin⟩ := (unitSphere_compact hpos).exists_isMinOn hn (continuous_deficit π C).continuousOn
  refine ⟨fun i => |f i|,fun i => abs_nonneg _,?_,?_⟩
  · rwa [squareMean_abs]
  · intro g hg
    exact (deficit_abs_le hπ.1 f hC).trans (hmin hg)

lemma normalize_squareMean {π : V → ℝ} (f : V → ℝ) (hS : 0 < squareMean π f) :
    squareMean π (fun i => (Real.sqrt (squareMean π f))⁻¹*f i)=1 := by
  rw [squareMean_smul,inv_pow,Real.sq_sqrt hS.le,inv_mul_cancel₀ hS.ne']

lemma normalize_deficit (π f : V → ℝ) (C : ℝ) (hS : 0 ≤ squareMean π f) :
    deficit π C (fun i => (Real.sqrt (squareMean π f))⁻¹*f i)=
      deficit π C f / squareMean π f := by
  rw [deficit_smul,inv_pow,Real.sq_sqrt hS,div_eq_mul_inv,mul_comm]

end LogSobolevMC.TwoPoint.Proof
-- End DeficitCompact

-- Begin DeficitDerivative

open scoped BigOperators
namespace LogSobolevMC.TwoPoint.Proof
open LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V] [DecidableEq V]

def perturb (f : V → ℝ) (i : V) (t : ℝ) : V → ℝ :=
  fun j => if j=i then f j+t else f j

omit [Fintype V] in
lemma perturb_zero (f : V → ℝ) (i : V) : perturb f i 0=f := by
  ext j
  simp [perturb]

omit [Fintype V] in
lemma perturb_deriv (f : V → ℝ) (i j : V) :
    HasDerivAt (fun t => perturb f i t j) (if j=i then 1 else 0) 0 := by
  by_cases h : j=i
  · simp only [perturb,if_pos h]
    exact (hasDerivAt_id (0:ℝ)).const_add (f j)
  · simp only [perturb,if_neg h]
    exact hasDerivAt_const _ _

lemma mean_perturb_deriv (π f : V → ℝ) (i : V) :
    HasDerivAt (fun t => mean π (perturb f i t)) (π i) 0 := by
  have h := HasDerivAt.fun_sum (fun j (_ : j ∈ Finset.univ) => (perturb_deriv f i j).const_mul (π j))
  simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true] at h
  exact h

lemma squareMean_perturb_deriv (π f : V → ℝ) (i : V) :
    HasDerivAt (fun t => squareMean π (perturb f i t)) (2*π i*f i) 0 := by
  have h := HasDerivAt.fun_sum (fun j (_ : j ∈ Finset.univ) =>
    ((perturb_deriv f i j).pow 2).const_mul (π j))
  simp only [perturb_zero,Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_ite,mul_one,mul_zero,
    Finset.sum_ite_eq',Finset.mem_univ,if_true] at h
  rw [show π i*(2*f i)=2*π i*f i by ring] at h
  exact h

lemma entropy_perturb_deriv (π f : V → ℝ) (i : V) (hS : 0 < squareMean π f) :
    HasDerivAt (fun t => entropy π (perturb f i t))
      (2*π i*f i*(Real.log ((f i)^2)-Real.log (squareMean π f))) 0 := by
  have ht (j : V) := ((squareLog_deriv (perturb f i 0 j)).comp
    (h := fun t => perturb f i t j) 0 (perturb_deriv f i j)).const_mul (π j)
  have hsum := HasDerivAt.fun_sum (fun j (_ : j ∈ Finset.univ) => ht j)
  simp only [perturb_zero,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true] at hsum
  have hlog := (Real.hasDerivAt_mul_log (x := squareMean π (perturb f i 0))
    (by simpa only [perturb_zero] using hS.ne')).comp
    (h := fun t => squareMean π (perturb f i t)) 0 (squareMean_perturb_deriv π f i)
  simp only [perturb_zero] at hlog
  have h := hsum.sub hlog
  have he : π i*(2*f i*(Real.log ((f i)^2)+1))-
      (Real.log (squareMean π f)+1)*(2*π i*f i)=
      2*π i*f i*(Real.log ((f i)^2)-Real.log (squareMean π f)) := by ring
  rw [he] at h
  exact h

lemma deficit_perturb_deriv (π f : V → ℝ) (C : ℝ) (i : V) (hS : 0 < squareMean π f) :
    HasDerivAt (fun t => deficit π C (perturb f i t))
      (2*π i*(C*(f i-mean π f)-f i*(Real.log ((f i)^2)-Real.log (squareMean π f)))) 0 := by
  have h := (((squareMean_perturb_deriv π f i).sub
    ((mean_perturb_deriv π f i).pow 2)).const_mul C).sub (entropy_perturb_deriv π f i hS)
  simp only [perturb_zero,Nat.cast_ofNat,Nat.reduceSub,pow_one] at h
  have he : C*(2*π i*f i-2*mean π f*π i)-
      2*π i*f i*(Real.log ((f i)^2)-Real.log (squareMean π f)) =
      2*π i*(C*(f i-mean π f)-f i*(Real.log ((f i)^2)-Real.log (squareMean π f))) := by ring
  rw [he] at h
  exact h

end LogSobolevMC.TwoPoint.Proof
-- End DeficitDerivative

-- Begin DeficitStationary

open Filter Topology
open scoped BigOperators
namespace LogSobolevMC.TwoPoint.Proof
open LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
lemma minimizer_ratio_le {π f : V → ℝ} {C : ℝ}
    (hmin : ∀ g, squareMean π g=1 → deficit π C f ≤ deficit π C g)
    (g : V → ℝ) (hS : 0 < squareMean π g) :
    deficit π C f ≤ deficit π C g / squareMean π g := by
  have h := hmin _ (normalize_squareMean g hS)
  rwa [normalize_deficit π g C hS.le] at h

lemma minimizer_stationary {π f : V → ℝ} {C : ℝ} (hpos : ∀ i, 0 < π i)
    (hu : squareMean π f=1)
    (hmin : ∀ g, squareMean π g=1 → deficit π C f ≤ deficit π C g) (i : V) :
    C*(f i-mean π f)-f i*Real.log ((f i)^2)=deficit π C f*f i := by
  have hS : 0 < squareMean π f := by rw [hu]; norm_num
  have hn : squareMean π (perturb f i 0) ≠ 0 := by rw [perturb_zero,hu]; norm_num
  have hd := (deficit_perturb_deriv π f C i hS).div (squareMean_perturb_deriv π f i) hn
  have hevent : ∀ᶠ t in 𝓝 (0:ℝ), 0 < squareMean π (perturb f i t) := by
    have h := (squareMean_perturb_deriv π f i).continuousAt
    apply h.preimage_mem_nhds
    apply Ioi_mem_nhds
    rwa [perturb_zero]
  have hlocal : IsLocalMin (fun t => deficit π C (perturb f i t)/squareMean π (perturb f i t)) 0 := by
    filter_upwards [hevent] with t ht
    simpa only [perturb_zero,hu,div_one] using minimizer_ratio_le hmin (perturb f i t) ht
  have hz := hlocal.hasDerivAt_eq_zero hd
  simp only [perturb_zero,hu,Real.log_one,sub_zero,mul_one,one_pow,div_one] at hz
  have hp := hpos i
  nlinarith only [hz,hp]

omit [DecidableEq V] in
lemma mean_pos_of_unit {π f : V → ℝ} (hpos : ∀ i, 0 < π i)
    (hf : ∀ i, 0 ≤ f i) (hu : squareMean π f=1) : 0 < mean π f := by
  have hn : 0 ≤ mean π f := Finset.sum_nonneg (fun i _ => mul_nonneg (hpos i).le (hf i))
  by_contra h
  have he : mean π f=0 := le_antisymm (le_of_not_gt h) hn
  have hz (i : V) : f i=0 := by
    have hi : π i*f i ≤ mean π f :=
      Finset.single_le_sum (fun j _ => mul_nonneg (hpos j).le (hf j)) (Finset.mem_univ i)
    rw [he] at hi
    exact le_antisymm ((mul_le_mul_iff_right₀ (hpos i)).mp (by simpa only [mul_zero,zero_mul,mul_comm] using hi)) (hf i)
  have hs : squareMean π f=0 := (squareMean_eq_zero_iff hpos f).mpr hz
  linarith

lemma minimizer_positive {π f : V → ℝ} {C : ℝ} (hpos : ∀ i, 0 < π i)
    (hC : 0 < C) (hf : ∀ i, 0 ≤ f i) (hu : squareMean π f=1)
    (hmin : ∀ g, squareMean π g=1 → deficit π C f ≤ deficit π C g) : ∀ i, 0 < f i := by
  intro i
  have h := minimizer_stationary hpos hu hmin i
  have hm := mean_pos_of_unit hpos hf hu
  by_contra hi
  have hz : f i=0 := le_antisymm (le_of_not_gt hi) (hf i)
  rw [hz] at h
  nlinarith only [h,mul_pos hC hm]

lemma minimizer_log_equation {π f : V → ℝ} {C : ℝ} (hpos : ∀ i, 0 < π i)
    (hu : squareMean π f=1)
    (hmin : ∀ g, squareMean π g=1 → deficit π C f ≤ deficit π C g) (i : V) :
    f i*Real.log (f i) = ((C-deficit π C f)/2)*f i-C*mean π f/2 := by
  have h := minimizer_stationary hpos hu hmin i
  rw [Real.log_pow] at h
  linear_combination -h / 2

end LogSobolevMC.TwoPoint.Proof
-- End DeficitStationary

-- Begin TwoValues

open scoped BigOperators
namespace LogSobolevMC.TwoPoint.Proof
open LogSobolevMC.ChiSquare.Proof

lemma no_three_log_affine {x y z A B : ℝ} (hx : 0 ≤ x) (hz : 0 ≤ z)
    (hxy : x<y) (hyz : y<z)
    (ex : x*Real.log x=A*x+B) (ey : y*Real.log y=A*y+B)
    (ez : z*Real.log z=A*z+B) : False := by
  have hzx : 0<z-x := by linarith
  let a := (z-y)/(z-x)
  let b := (y-x)/(z-x)
  have ha : 0<a := div_pos (sub_pos.mpr hyz) hzx
  have hb : 0<b := div_pos (sub_pos.mpr hxy) hzx
  have hab : a+b=1 := by dsimp [a,b]; field_simp; ring
  have he : a*x+b*z=y := by dsimp [a,b]; field_simp; ring
  have h := Real.strictConvexOn_mul_log.2 hx hz (ne_of_lt (hxy.trans hyz)) ha hb hab
  simp only [smul_eq_mul] at h
  rw [he,ex,ey,ez] at h
  have he' : a*(A*x+B)+b*(A*z+B)=A*y+B := by
    calc
      _ = A*(a*x+b*z)+B*(a+b) := by ring
      _ = _ := by rw [he,hab,mul_one]
  rw [he'] at h
  exact (lt_irrefl _ h)

lemma two_values_of_log_affine {V : Type*} [Fintype V] [Nonempty V]
    (f : V → ℝ) (hf : ∀ i, 0 ≤ f i) (A B : ℝ)
    (he : ∀ i, f i*Real.log (f i)=A*f i+B) :
    ∃ i j : V, ∀ k, f k=f i ∨ f k=f j := by
  obtain ⟨i,_,hi⟩ := Finset.exists_min_image Finset.univ f Finset.univ_nonempty
  obtain ⟨j,_,hj⟩ := Finset.exists_max_image Finset.univ f Finset.univ_nonempty
  refine ⟨i,j,fun k => ?_⟩
  by_cases hki : f k=f i
  · exact Or.inl hki
  by_cases hkj : f k=f j
  · exact Or.inr hkj
  exact False.elim (no_three_log_affine (hf i) (hf j)
    (lt_of_le_of_ne (hi k (Finset.mem_univ k)) (Ne.symm hki))
    (lt_of_le_of_ne (hj k (Finset.mem_univ k)) hkj) (he i) (he k) (he j))

lemma minimizer_two_values {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {π f : V → ℝ} {C : ℝ} (hpos : ∀ i, 0 < π i) (hf : ∀ i, 0 ≤ f i)
    (hu : squareMean π f=1)
    (hmin : ∀ g, squareMean π g=1 → deficit π C f ≤ deficit π C g) :
    ∃ i j : V, ∀ k, f k=f i ∨ f k=f j := by
  apply two_values_of_log_affine f hf ((C-deficit π C f)/2) (-C*mean π f/2)
  intro i
  have h := minimizer_log_equation hpos hu hmin i
  linarith only [h]

end LogSobolevMC.TwoPoint.Proof
-- End TwoValues

-- Begin TwoPointAggregation

open scoped BigOperators
namespace LogSobolevMC.TwoPoint.Proof
open LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def groupMass (π : V → ℝ) (S : Finset V) : ℝ := ∑ i ∈ S, π i

def twoFunction (S : Finset V) (a b : ℝ) : V → ℝ := fun i => if i ∈ S then a else b

lemma weighted_twoFunction (π : V → ℝ) (hπ : ∑ i,π i=1) (S : Finset V)
    (a b : ℝ) (F : ℝ → ℝ) :
    (∑ i,π i*F (twoFunction S a b i))=groupMass π S*F a+(1-groupMass π S)*F b := by
  have hp : (∑ i, if i∈S then π i else 0)=groupMass π S := by
    simp only [groupMass,Finset.sum_ite_mem,Finset.univ_inter]
  have hq : (∑ i,if i∈S then 0 else π i)=1-groupMass π S := by
    have hh : (∑ i,if i∈S then π i else 0)+(∑ i,if i∈S then 0 else π i)=1 := by
      rw [←Finset.sum_add_distrib]
      simpa only [ite_add_ite,add_zero,zero_add,ite_self] using hπ
    linarith only [hh,hp]
  calc
    _ = (∑ i,if i∈S then π i else 0)*F a+(∑ i,if i∈S then 0 else π i)*F b := by
      rw [Finset.sum_mul,Finset.sum_mul,←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i∈S <;> simp [twoFunction,hi]
    _ = _ := by rw [hp,hq]

lemma twoFunction_mean (π : V → ℝ) (hπ : ∑ i,π i=1) (S : Finset V) (a b : ℝ) :
    mean π (twoFunction S a b)=groupMass π S*a+(1-groupMass π S)*b :=
  weighted_twoFunction π hπ S a b id

lemma twoFunction_squareMean (π : V → ℝ) (hπ : ∑ i,π i=1) (S : Finset V) (a b : ℝ) :
    squareMean π (twoFunction S a b)=groupMass π S*a^2+(1-groupMass π S)*b^2 :=
  weighted_twoFunction π hπ S a b (fun t => t^2)

lemma twoFunction_entropy (π : V → ℝ) (hπ : ∑ i,π i=1) (S : Finset V) (a b : ℝ) :
    entropy π (twoFunction S a b)=scalarEntropy (groupMass π S) a b := by
  rw [entropy,weighted_twoFunction π hπ S a b squareLog,twoFunction_squareMean π hπ]
  unfold squareLog scalarEntropy
  ring

lemma twoFunction_variance (π : V → ℝ) (hπ : ∑ i,π i=1) (S : Finset V) (a b : ℝ) :
    squareMean π (twoFunction S a b)-(mean π (twoFunction S a b))^2=
      groupMass π S*(1-groupMass π S)*(a-b)^2 := by
  rw [twoFunction_squareMean π hπ,twoFunction_mean π hπ]
  ring

lemma groupMass_compl (π : V → ℝ) (hπ : ∑ i,π i=1) (S : Finset V) :
    groupMass π Sᶜ=1-groupMass π S := by
  have h : groupMass π S+groupMass π Sᶜ=1 := by
    rw [groupMass,groupMass,Finset.sum_add_sum_compl,hπ]
  linarith

omit [DecidableEq V] in
lemma groupMass_min [Nonempty V] {π : V → ℝ} (hπ : ∀ i,0≤π i)
    {S : Finset V} (hS : S.Nonempty) : piMin π ≤ groupMass π S := by
  obtain ⟨i,hi⟩ := hS
  exact (Finset.inf'_le _ (Finset.mem_univ i)).trans
    (Finset.single_le_sum (fun j _ => hπ j) hi)

omit [DecidableEq V] in
lemma piMin_pos [Nonempty V] {π : V → ℝ} (hπ : ∀ i,0<π i) : 0<piMin π :=
  (Finset.lt_inf'_iff Finset.univ_nonempty).mpr (fun i _ => hπ i)

end LogSobolevMC.TwoPoint.Proof
-- End TwoPointAggregation

-- Begin PartitionBound

namespace LogSobolevMC.TwoPoint.Proof
open LogSobolevMC.ChiSquare.Proof

lemma scalarEntropy_swap (p a b : ℝ) : scalarEntropy p a b=scalarEntropy (1-p) b a := by
  have he : (1-p)*b^2+(1-(1-p))*a^2=p*a^2+(1-p)*b^2 := by ring
  unfold scalarEntropy
  rw [he]
  ring

lemma scalarEntropy_le_min {m p a b : ℝ} (hm : 0 < m) (hmp : m ≤ p) (hmq : m ≤ 1-p)
    (ha : 0≤a) (hb : 0≤b) :
    scalarEntropy p a b ≤ coeff m*(p*(1-p)*(a-b)^2) := by
  have hp : 0<p := hm.trans_le hmp
  have hq : 0<1-p := hm.trans_le hmq
  by_cases hh : p≤1/2
  · calc
      _ ≤ coeff p*(p*(1-p)*(a-b)^2) := by
        convert scalarEntropy_le hp hh ha hb using 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (coeff_antitone hm hmp hh)
        (mul_nonneg (mul_nonneg hp.le hq.le) (sq_nonneg _))
  · have hhq : 1-p≤1/2 := by linarith
    rw [scalarEntropy_swap]
    calc
      _ ≤ coeff (1-p)*((1-p)*p*(b-a)^2) := by
        convert scalarEntropy_le hq hhq hb ha using 1; ring
      _ ≤ coeff m*((1-p)*p*(b-a)^2) :=
        mul_le_mul_of_nonneg_right (coeff_antitone hm hmq hhq)
          (mul_nonneg (mul_nonneg hq.le hp.le) (sq_nonneg _))
      _ = _ := by ring

lemma deficit_twoFunction_nonneg {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {π : V → ℝ} (hπ : MarkovMixing.IsDist π) (hpos : ∀i,0<π i)
    {S : Finset V} (hS : S.Nonempty) (hSc : Sᶜ.Nonempty) {a b : ℝ} (ha : 0≤a) (hb : 0≤b) :
    0≤deficit π (coeff (piMin π)) (twoFunction S a b) := by
  have hm := piMin_pos hpos
  have hmp := groupMass_min hπ.1 hS
  have hmq := groupMass_min hπ.1 hSc
  rw [groupMass_compl π hπ.2] at hmq
  have h := scalarEntropy_le_min hm hmp hmq ha hb
  rw [deficit,twoFunction_variance π hπ.2,twoFunction_entropy π hπ.2]
  linarith only [h]

end LogSobolevMC.TwoPoint.Proof
-- End PartitionBound

-- Begin GeneralSharp

open scoped BigOperators
namespace LogSobolevMC.TwoPoint.Proof
open LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

omit [DecidableEq V] [Nonempty V] in
lemma deficit_const {π : V → ℝ} (hπ : ∑i,π i=1) (C c : ℝ) :
    deficit π C (fun _ => c)=0 := by
  have hS : squareMean π (fun _ => c)=c^2 := by
    simp only [squareMean,←Finset.sum_mul,hπ,one_mul]
  have hE : entropy π (fun _ => c)=0 := by
    simp only [entropy,hS,←Finset.sum_mul,hπ,one_mul,squareLog,sub_self]
  rw [deficit,hS,mean_const hπ,hE,sub_self,mul_zero,sub_self]

lemma two_valued_deficit_nonneg {π f : V → ℝ} (hπ : MarkovMixing.IsDist π)
    (hpos : ∀i,0<π i) (hf : ∀i,0≤f i)
    (ht : ∃ i j : V, ∀k,f k=f i ∨ f k=f j) :
    0≤deficit π (coeff (piMin π)) f := by
  classical
  obtain ⟨i,j,hij⟩ := ht
  by_cases he : f i=f j
  · have hconst : f=fun _ => f i := by
      ext k
      rcases hij k with h|h
      · exact h
      · exact h.trans he.symm
    rw [hconst,deficit_const hπ.2]
  · let S := Finset.univ.filter (fun k => f k=f i)
    have hi : i∈S := by simp [S]
    have hj : j∈Sᶜ := by simp [S,ne_comm,he]
    have htwo : f=twoFunction S (f i) (f j) := by
      ext k
      by_cases hk : k∈S
      · simpa only [twoFunction,if_pos hk] using (Finset.mem_filter.mp hk).2
      · have hki : f k≠f i := by simpa [S] using hk
        simpa only [twoFunction,if_neg hk] using (hij k).resolve_left hki
    rw [htwo]
    exact deficit_twoFunction_nonneg hπ hpos ⟨i,hi⟩ ⟨j,hj⟩ (hf i) (hf j)

lemma deficit_nonneg {π : V → ℝ} (hπ : MarkovMixing.IsDist π)
    (hpos : ∀i,0<π i) (hhalf : piMin π<1/2) (g : V → ℝ) :
    0≤deficit π (coeff (piMin π)) g := by
  have hC := coeff_nonneg (piMin_pos hpos) hhalf.le
  obtain ⟨f,hf,hu,hmin⟩ := deficit_minimizer hπ hpos hC
  have hnf := two_valued_deficit_nonneg hπ hpos hf (minimizer_two_values hpos hf hu hmin)
  by_cases hz : squareMean π g=0
  · have hg := (squareMean_eq_zero_iff hpos g).mp hz
    have he : g=fun _ => 0 := funext hg
    rw [he,deficit_const hπ.2]
  · have hs : 0<squareMean π g := lt_of_le_of_ne (squareMean_nonneg hπ.1 g) (Ne.symm hz)
    have h := hnf.trans (minimizer_ratio_le hmin g hs)
    simpa only [zero_mul] using (le_div_iff₀ hs).mp h

lemma entropy_le_sharp_variance {π : V → ℝ} (hπ : MarkovMixing.IsDist π)
    (hpos : ∀i,0<π i) (hhalf : piMin π<1/2) (f : V → ℝ) :
    LogSobolevMC.ChiSquare.entL π f ≤ coeff (piMin π)*MarkovMixing.distVar π f := by
  have h := deficit_nonneg hπ hpos hhalf f
  rw [deficit,entropy_native hpos,←variance_eq_squareMean hπ.2] at h
  linarith only [h]

end LogSobolevMC.TwoPoint.Proof
-- End GeneralSharp

-- Begin NativeRefresh

open scoped BigOperators
namespace LogSobolevMC.TwoPoint.Proof
open LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
lemma indep_stationary {π : V → ℝ} (hπ : MarkovMixing.IsDist π) :
    MarkovMixing.IsStationary (indepChain π) π := by
  refine ⟨hπ,?_⟩
  ext j
  simp only [Matrix.vecMul,dotProduct,indepChain,←Finset.sum_mul,hπ.2,one_mul]

omit [DecidableEq V] in
lemma indep_dirichlet {π : V → ℝ} (hπ : ∑i,π i=1) (f : V → ℝ) :
    LogSobolevMC.ChiSquare.dirichlet (indepChain π) π f f=MarkovMixing.distVar π f := by
  rw [variance_eq_squareMean hπ]
  change (∑i,(f i-mean π f)*f i*π i)=squareMean π f-(mean π f)^2
  calc
    _ = (∑i,π i*(f i)^2)-mean π f*(∑i,π i*f i) := by
      rw [Finset.mul_sum,←Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by change squareMean π f-mean π f*mean π f=_; ring

lemma coeff_inv_formula {p : ℝ} (hp : 0<p) (hp' : p<1/2) :
    (coeff p)⁻¹=(1-2*p)/Real.log (1/p-1) := by
  rw [coeff,if_neg (ne_of_lt hp'),inv_div]
  have he : (1-p)/p=1/p-1 := by field_simp
  rw [he]

end LogSobolevMC.TwoPoint.Proof
-- End NativeRefresh

-- Begin SharpWitness

open scoped BigOperators
namespace LogSobolevMC.TwoPoint.Proof
open LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

lemma sharp_ratio_witness {π : V → ℝ} (hπ : MarkovMixing.IsDist π)
    (hpos : ∀i,0<π i) (hhalf : piMin π<1/2) :
    ∃ f : V → ℝ, 0<LogSobolevMC.ChiSquare.entL π f ∧
      LogSobolevMC.ChiSquare.dirichlet (indepChain π) π f f /
        LogSobolevMC.ChiSquare.entL π f = (coeff (piMin π))⁻¹ := by
  classical
  obtain ⟨i,_,he⟩ := Finset.exists_mem_eq_inf' (s := Finset.univ) Finset.univ_nonempty π
  have hp := piMin_pos hpos
  have hC := coeff_pos hp hhalf.le
  have hq : 0<1-piMin π := by linarith
  have hr := ratio_gt_one hp hhalf
  let f := twoFunction ({i} : Finset V) ((1-piMin π)/piMin π) 1
  have hm : groupMass π ({i} : Finset V)=piMin π := by
    simp only [groupMass,Finset.sum_singleton]
    exact he.symm
  let v := piMin π*(1-piMin π)*(((1-piMin π)/piMin π)-1)^2
  have hv : 0<v := mul_pos (mul_pos hp hq) (sq_pos_of_pos (sub_pos.mpr hr))
  have hvar : MarkovMixing.distVar π f=v := by
    rw [variance_eq_squareMean hπ.2]
    dsimp only [f]
    rw [twoFunction_variance π hπ.2,hm]
  have hE : LogSobolevMC.ChiSquare.entL π f=coeff (piMin π)*v := by
    rw [←entropy_native hpos]
    dsimp only [f]
    rw [twoFunction_entropy π hπ.2,hm,scalarEntropy_sharp hp hhalf]
    dsimp only [v]
    ring
  refine ⟨f,by rw [hE]; exact mul_pos hC hv,?_⟩
  rw [indep_dirichlet hπ.2,hvar,hE]
  field_simp

end LogSobolevMC.TwoPoint.Proof
-- End SharpWitness

-- Begin NativeInfimum

namespace LogSobolevMC.TwoPoint.Proof
open LogSobolevMC.ChiSquare.Proof
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

lemma indep_logSobolev {π : V → ℝ} (hπ : MarkovMixing.IsDist π)
    (hpos : ∀i,0<π i) (hhalf : piMin π<1/2) :
    LogSobolevMC.ChiSquare.logSobolev (indepChain π) π =
      (1-2*piMin π)/Real.log (1/piMin π-1) := by
  have hp := piMin_pos hpos
  have hC := coeff_pos hp hhalf.le
  let T := {r : ℝ | ∃ f : V → ℝ, LogSobolevMC.ChiSquare.entL π f≠0 ∧
    r=LogSobolevMC.ChiSquare.dirichlet (indepChain π) π f f / LogSobolevMC.ChiSquare.entL π f}
  have hlower : ∀ r∈T, (coeff (piMin π))⁻¹≤r := by
    rintro r ⟨f,hf,rfl⟩
    have hE : 0<LogSobolevMC.ChiSquare.entL π f :=
      lt_of_le_of_ne (entL_nonneg_dist hπ hpos f) hf.symm
    have h := entropy_le_sharp_variance hπ hpos hhalf f
    rw [indep_dirichlet hπ.2]
    apply (le_div_iff₀ hE).mpr
    have hd : LogSobolevMC.ChiSquare.entL π f/coeff (piMin π)≤MarkovMixing.distVar π f :=
      (div_le_iff₀ hC).mpr (by simpa only [mul_comm] using h)
    simpa only [div_eq_mul_inv,mul_comm] using hd
  obtain ⟨f,hf,he⟩ := sharp_ratio_witness hπ hpos hhalf
  have hm : (coeff (piMin π))⁻¹∈T := ⟨f,hf.ne',he.symm⟩
  have hb : BddBelow T := ⟨_,hlower⟩
  change sInf T=_
  rw [←coeff_inv_formula hp hhalf]
  exact le_antisymm (csInf_le hb hm) (le_csInf ⟨_,hm⟩ hlower)

end LogSobolevMC.TwoPoint.Proof
-- End NativeInfimum

-- Begin RootAssembly

open scoped BigOperators
namespace LogSobolevMC.TwoPoint.Proof

lemma uniform_dist {V : Type*} [Fintype V] [Nonempty V] :
    MarkovMixing.IsDist (MarkovMixing.uniformDist V) := by
  refine ⟨fun _ => inv_nonneg.mpr (Nat.cast_nonneg _),?_⟩
  simp [MarkovMixing.uniformDist,Fintype.card_ne_zero]

lemma uniform_piMin {V : Type*} [Fintype V] [Nonempty V] :
    piMin (MarkovMixing.uniformDist V)=(Fintype.card V : ℝ)⁻¹ := by
  exact Finset.inf'_const Finset.univ_nonempty _

end LogSobolevMC.TwoPoint.Proof

namespace LogSobolevMC.TwoPoint
open MarkovMixing Proof

theorem theorem_A_1 {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (π : V → ℝ) (hπ : IsDist π) (hπpos : ∀ x, 0 < π x) (hhalf : piMin π < 1 / 2) :
    IsStationary (indepChain π) π ∧
    LogSobolevMC.ChiSquare.logSobolev (indepChain π) π = (1 - 2 * piMin π) / Real.log (1 / piMin π - 1) ∧
      (3 ≤ Fintype.card V →
        LogSobolevMC.ChiSquare.logSobolev (indepChain (uniformDist V)) (uniformDist V) =
          (1 - 2 / (Fintype.card V : ℝ)) / Real.log ((Fintype.card V : ℝ) - 1)) := by
  refine ⟨indep_stationary hπ,indep_logSobolev hπ hπpos hhalf,?_⟩
  intro hn
  have hn' : (3:ℝ)≤Fintype.card V := by exact_mod_cast hn
  have hp : (0:ℝ)<Fintype.card V := by linarith
  have hpos : ∀i : V,0<uniformDist V i := fun _ => inv_pos.mpr hp
  have hh : piMin (uniformDist V)<1/2 := by
    rw [uniform_piMin,←one_div]
    apply (div_lt_div_iff₀ hp (by norm_num : (0:ℝ)<2)).mpr
    nlinarith only [hn']
  have h := indep_logSobolev uniform_dist hpos hh
  rw [uniform_piMin] at h
  simpa only [one_div,inv_inv,div_eq_mul_inv,one_mul] using h

end LogSobolevMC.TwoPoint
-- End RootAssembly

-- Begin Solution

open MarkovMixing LogSobolevMC.TwoPoint

theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (π : V → ℝ) (hπ : IsDist π) (hπpos : ∀ x, 0 < π x) (hhalf : piMin π < 1 / 2) :
    IsStationary (indepChain π) π ∧
    LogSobolevMC.ChiSquare.logSobolev (indepChain π) π = (1 - 2 * piMin π) / Real.log (1 / piMin π - 1) ∧
      (3 ≤ Fintype.card V →
        LogSobolevMC.ChiSquare.logSobolev (indepChain (uniformDist V)) (uniformDist V) =
          (1 - 2 / (Fintype.card V : ℝ)) / Real.log ((Fintype.card V : ℝ) - 1)) :=
  theorem_A_1 π hπ hπpos hhalf
-- End Solution
