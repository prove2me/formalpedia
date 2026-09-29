-- Prove2me | solution 1 for GeneralCK.Certificates.BivariateProvedProgram.value_pos_of_accepted_taylor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-24T23:01:37.724561+00:00
-- url     : https://prove2.me/submissions/f2628d4a-b9ab-452b-841e-5a4f01a6637d

import Definitions.Def_GeneralCK_E8_interval_checkers
import Definitions.Def_GeneralCK_E8_semantic_core
import Definitions.Def_GeneralCK_RB2_checker_semantics_v2
import Definitions.Def_GeneralCK_RB2_program_data
import Definitions.Def_GeneralCK_bellman
import Definitions.Def_GeneralCK_entropy_comparison
import Definitions.Def_GeneralCK_statement
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.DivMod
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.MonotoneContinuity
import Theorems.Thm_GeneralCK_H_pos
import Theorems.Thm_GeneralCK_H_strictMonoOn

section
namespace GeneralCK.Certificates



namespace Jet2
open scoped Topology






















theorem SoundAt.add {j k : Jet2} {t : ℝ} (hj : j.SoundAt t) (hk : k.SoundAt t) :
    (j.add k).SoundAt t := ⟨hj.1.add hk.1, hj.2.add hk.2⟩

theorem SoundAt.neg {j : Jet2} {t : ℝ} (hj : j.SoundAt t) :
    j.neg.SoundAt t := ⟨hj.1.neg, hj.2.neg⟩

theorem SoundAt.mul {j k : Jet2} {t : ℝ} (hj : j.SoundAt t) (hk : k.SoundAt t) :
    (j.mul k).SoundAt t := by
  refine ⟨hj.1.mul hk.1, ?_⟩
  have hh := (hj.2.mul hk.1).add (hj.1.mul hk.2)
  convert! hh using 1
  simp only [Jet2.mul]
  ring

theorem SoundAt.inv {j : Jet2} {t : ℝ} (hj : j.SoundAt t) (hn : j.value t ≠ 0) :
    j.inv.SoundAt t := by
  constructor
  · convert! hj.1.inv hn using 1
  · have hh := hj.2.neg.div (hj.1.pow 2) (pow_ne_zero 2 hn)
    convert! hh using 1
    simp only [Jet2.inv, Pi.pow_apply, Pi.neg_apply]
    field_simp [hn]
    ring

theorem SoundAt.log {j : Jet2} {t : ℝ} (hj : j.SoundAt t) (hn : j.value t ≠ 0) :
    j.log.SoundAt t := by
  refine ⟨hj.1.log hn, ?_⟩
  have hh := hj.2.div hj.1 hn
  convert! hh using 1
  simp only [Jet2.log]
  field_simp [hn]





















end Jet2
end GeneralCK.Certificates
end

section
namespace GeneralCK.Certificates.Jet2



theorem SoundAt.comp {j k : Jet2} {t : ℝ} (hj : j.SoundAt (k.value t))
    (hk : k.SoundAt t) : (j.comp k).SoundAt t := by
  refine ⟨hj.1.comp t hk.1, ?_⟩
  have hh := (hj.2.comp t hk.1).mul hk.2
  convert! hh using 1
  simp only [Jet2.comp, Function.comp_apply]
  ring



end GeneralCK.Certificates.Jet2
end

section
namespace GeneralCK.Certificates



namespace DyadicInterval



theorem scale_pos (p : ℕ) : 0 < scale p := by unfold scale; positivity
theorem scale_cast_pos (p : ℕ) : 0 < (scale p : ℝ) := by exact_mod_cast scale_pos p











theorem floorDiv_mul_le (z : ℤ) {d : ℤ} (hd : 0 < d) : floorDiv z d*d ≤ z :=
  Int.ediv_mul_le z hd.ne'

theorem le_ceilDiv_mul (z : ℤ) {d : ℤ} (hd : 0 < d) : z ≤ ceilDiv z d*d := by
  have h := floorDiv_mul_le (-z) hd
  unfold floorDiv ceilDiv at *
  nlinarith








theorem ofInt_sound (p : ℕ) (z : ℤ) : (ofInt p z).Contains (z : ℝ) := by
  simp [Contains, ofInt]

theorem add_sound {p : ℕ} {a b : DyadicInterval p} {x y : ℝ}
    (hx : a.Contains x) (hy : b.Contains y) : (a.add b).Contains (x+y) := by
  rcases hx with ⟨hlx, hux⟩
  rcases hy with ⟨hly, huy⟩
  dsimp [Contains, add]
  push_cast
  constructor <;> nlinarith

theorem neg_sound {p : ℕ} {a : DyadicInterval p} {x : ℝ}
    (hx : a.Contains x) : a.neg.Contains (-x) := by
  rcases hx with ⟨hl, hu⟩
  dsimp [Contains, neg]
  push_cast
  constructor <;> nlinarith

theorem sub_sound {p : ℕ} {a b : DyadicInterval p} {x y : ℝ}
    (hx : a.Contains x) (hy : b.Contains y) : (a.sub b).Contains (x-y) := by
  simpa only [sub, sub_eq_add_neg] using add_sound hx (neg_sound hy)

private theorem linear_bounds {lo hi x c : ℝ} (hl : lo ≤ x) (hh : x ≤ hi) :
    min (lo*c) (hi*c) ≤ x*c ∧ x*c ≤ max (lo*c) (hi*c) := by
  by_cases hc : 0 ≤ c
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_right hl hc),
      (mul_le_mul_of_nonneg_right hh hc).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_right hh (not_le.mp hc).le),
      (mul_le_mul_of_nonpos_right hl (not_le.mp hc).le).trans (le_max_left _ _)⟩

private theorem product_bounds {al ah bl bh x y : ℝ}
    (hx : al ≤ x ∧ x ≤ ah) (hy : bl ≤ y ∧ y ≤ bh) :
    min (min (al*bl) (al*bh)) (min (ah*bl) (ah*bh)) ≤ x*y ∧
      x*y ≤ max (max (al*bl) (al*bh)) (max (ah*bl) (ah*bh)) := by
  have h := linear_bounds (c := y) hx.1 hx.2
  have hl := linear_bounds (c := al) hy.1 hy.2
  have hh := linear_bounds (c := ah) hy.1 hy.2
  simp only [mul_comm y al, mul_comm y ah, mul_comm bl al, mul_comm bh al,
    mul_comm bl ah, mul_comm bh ah] at hl hh
  exact ⟨(min_le_min hl.1 hh.1).trans h.1, h.2.trans (max_le_max hl.2 hh.2)⟩

theorem mul_sound {p : ℕ} {a b : DyadicInterval p} {x y : ℝ}
    (hx : a.Contains x) (hy : b.Contains y) : (a.mul b).Contains (x*y) := by
  have hp := product_bounds hx hy
  have hlo : (productLo a b : ℝ) ≤ ((scale p : ℝ)*x)*((scale p : ℝ)*y) := by
    simpa [productLo, or_assoc] using hp.1
  have hhi : ((scale p : ℝ)*x)*((scale p : ℝ)*y) ≤ (productHi a b : ℝ) := by
    simpa [productHi, or_assoc] using hp.2
  have hroundL : ((floorDiv (productLo a b) (scale p) : ℤ) : ℝ)*(scale p : ℝ) ≤ (productLo a b : ℝ) := by
    exact_mod_cast floorDiv_mul_le (productLo a b) (scale_pos p)
  have hroundH : (productHi a b : ℝ) ≤ ((ceilDiv (productHi a b) (scale p) : ℤ) : ℝ)*(scale p : ℝ) := by
    exact_mod_cast le_ceilDiv_mul (productHi a b) (scale_pos p)
  have hs := scale_cast_pos p
  constructor
  · change (floorDiv (productLo a b) (scale p) : ℝ) ≤ (scale p : ℝ)*(x*y)
    apply (mul_le_mul_iff_left₀ hs).mp
    nlinarith [hroundL.trans hlo]
  · change (scale p : ℝ)*(x*y) ≤ (ceilDiv (productHi a b) (scale p) : ℝ)
    apply (mul_le_mul_iff_left₀ hs).mp
    nlinarith [hhi.trans hroundH]

theorem recip_sound {p : ℕ} {a : DyadicInterval p} {x : ℝ}
    (ha : 0 < a.lo) (hx : a.Contains x) : a.recip.Contains (x⁻¹) := by
  have hs := scale_cast_pos p
  have hlo : (0:ℝ) < a.lo := by exact_mod_cast ha
  have hxpos : 0 < x := pos_of_mul_pos_right (hlo.trans_le hx.1) hs.le
  have hhi : (0:ℝ) < a.hi := (mul_pos hs hxpos).trans_le hx.2
  have hhiZ : 0 < a.hi := by exact_mod_cast hhi
  have hrL : (floorDiv (scale p*scale p) a.hi : ℝ)*(a.hi : ℝ) ≤ (scale p : ℝ)^2 := by
    have h := floorDiv_mul_le (scale p*scale p) hhiZ
    exact_mod_cast (by simpa only [pow_two] using h : floorDiv (scale p*scale p) a.hi*a.hi ≤ (scale p)^2)
  have hrH : (scale p : ℝ)^2 ≤ (ceilDiv (scale p*scale p) a.lo : ℝ)*(a.lo : ℝ) := by
    have h := le_ceilDiv_mul (scale p*scale p) ha
    exact_mod_cast (by simpa only [pow_two] using h : (scale p)^2 ≤ ceilDiv (scale p*scale p) a.lo*a.lo)
  constructor
  · change (floorDiv (scale p*scale p) a.hi : ℝ) ≤ (scale p : ℝ)*x⁻¹
    rw [← div_eq_mul_inv]
    calc
      _ ≤ (scale p : ℝ)^2/(a.hi : ℝ) := (le_div_iff₀ hhi).mpr hrL
      _ ≤ (scale p : ℝ)/x := by
        apply (div_le_div_iff₀ hhi hxpos).mpr
        nlinarith [mul_le_mul_of_nonneg_left hx.2 hs.le]
  · change (scale p : ℝ)*x⁻¹ ≤ (ceilDiv (scale p*scale p) a.lo : ℝ)
    rw [← div_eq_mul_inv]
    calc
      _ ≤ (scale p : ℝ)^2/(a.lo : ℝ) := by
        apply (div_le_div_iff₀ hxpos hlo).mpr
        nlinarith [mul_le_mul_of_nonneg_left hx.1 hs.le]
      _ ≤ _ := (div_le_iff₀ hlo).mpr hrH




theorem subsetCheck_sound {p : ℕ} {a b : DyadicInterval p}
    (h : a.subsetCheck b=true) {x : ℝ} (hx : a.Contains x) : b.Contains x := by
  have hh : b.lo ≤ a.lo ∧ a.hi ≤ b.hi := by simpa [subsetCheck] using h
  have hl : (b.lo : ℝ) ≤ (a.lo : ℝ) := by exact_mod_cast hh.1
  have hu : (a.hi : ℝ) ≤ (b.hi : ℝ) := by exact_mod_cast hh.2
  exact ⟨hl.trans hx.1, hx.2.trans hu⟩

theorem positiveCheck_sound {p : ℕ} {a : DyadicInterval p}
    (h : a.positiveCheck=true) {x : ℝ} (hx : a.Contains x) : 0 < x := by
  have ha : 0 < a.lo := by simpa [positiveCheck] using h
  have ha' : (0:ℝ) < a.lo := by exact_mod_cast ha
  exact pos_of_mul_pos_right (ha'.trans_le hx.1) (scale_cast_pos p).le









end DyadicInterval
end GeneralCK.Certificates
end

section
namespace GeneralCK
open scoped BigOperators















theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

@[simp] theorem H_zero : H 0 = 0 := by simp [H]
@[simp] theorem H_one : H 1 = 0 := by simp [H]
@[simp] theorem H_half : H (1 / 2) = 1 := by
  have h : Real.log 2 ≠ 0 := ne_of_gt log_two_pos
  simpa [H, one_div] using div_self h







theorem H_continuous : Continuous H :=
  Real.binEntropy_continuous.div_const _

end GeneralCK
end

section
namespace GeneralCK

/-- The contact equation has exactly one solution in the open lower half. -/
theorem existsUnique_radialContact {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    ∃! v : ℝ, 0 < v ∧ v < 1 / 2 ∧ z * H v = h * (1 - 2 * v) := by
  let g : ℝ → ℝ := fun v => z * H v - h * (1 - 2 * v)
  have hg : Continuous g :=
    (H_continuous.const_mul z).sub
      ((continuous_const.sub (continuous_const.mul continuous_id)).const_mul h)
  have hzero : g 0 = -h := by simp [g]
  have hhalf : g (1 / 2) = z := by simp only [g, H_half]; ring
  have himage := intermediate_value_Icc (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    hg.continuousOn
  obtain ⟨v, hv, heq⟩ := himage (show (0 : ℝ) ∈ Set.Icc (g 0) (g (1 / 2)) by
    rw [hzero, hhalf]; exact ⟨by linarith, hz.le⟩)
  have hv0 : 0 < v := by
    apply lt_of_le_of_ne hv.1
    intro he
    rw [← he, hzero] at heq
    linarith
  have hv1 : v < 1 / 2 := by
    apply lt_of_le_of_ne hv.2
    intro he
    rw [he, hhalf] at heq
    linarith
  have hveq : z * H v = h * (1 - 2 * v) := sub_eq_zero.mp heq
  refine ⟨v, ⟨hv0, hv1, hveq⟩, ?_⟩
  rintro u ⟨hu0, hu1, hueq⟩
  rcases lt_trichotomy u v with huv | huv | huv
  · have hH := H_strictMonoOn ⟨hu0.le, hu1.le⟩ ⟨hv0.le, hv1.le⟩ huv
    have hm := mul_lt_mul_of_pos_left hH hz
    nlinarith
  · exact huv
  · have hH := H_strictMonoOn ⟨hv0.le, hv1.le⟩ ⟨hu0.le, hu1.le⟩ huv
    have hm := mul_lt_mul_of_pos_left hH hz
    nlinarith

theorem radialContact_spec {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    0 < radialContact z h ∧ radialContact z h < 1 / 2 ∧
      z * H (radialContact z h) = h * (1 - 2 * radialContact z h) := by
  obtain ⟨v, hv, huniq⟩ := existsUnique_radialContact hz hh
  have hset : {u : ℝ | 0 < u ∧ u < 1 / 2 ∧ z * H u = h * (1 - 2 * u)} = {v} := by
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    exact ⟨fun hu => huniq u hu, fun he => he ▸ hv⟩
  simpa only [radialContact, hset, csInf_singleton] using hv

theorem radialContact_pos {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    0 < radialContact z h := (radialContact_spec hz hh).1

theorem radialContact_lt_half {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    radialContact z h < 1 / 2 := (radialContact_spec hz hh).2.1

theorem radialContact_equation {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    z * H (radialContact z h) = h * (1 - 2 * radialContact z h) :=
  (radialContact_spec hz hh).2.2

theorem radialContact_eq_of_equation {z h v : ℝ} (hz : 0 < z) (hh : 0 < h)
    (hv : 0 < v) (hv' : v < 1 / 2) (heq : z * H v = h * (1 - 2 * v)) :
    radialContact z h = v := by
  obtain ⟨u, _, huniq⟩ := existsUnique_radialContact hz hh
  exact (huniq _ (radialContact_spec hz hh)).trans (huniq v ⟨hv, hv', heq⟩).symm

/-- Simultaneous nonzero scaling leaves the defining root set unchanged. -/
theorem radialContact_scale (z h : ℝ) {c : ℝ} (hc : c ≠ 0) :
    radialContact (c * z) (c * h) = radialContact z h := by
  unfold radialContact
  congr 1
  ext v
  simp only [Set.mem_ofPred_eq, mul_assoc, mul_right_inj' hc]







theorem radialContact_strictAnti_radius {a b h : ℝ}
    (ha : 0 < a) (hab : a < b) (hh : 0 < h) :
    radialContact b h < radialContact a h := by
  obtain ⟨hu, hu', hequ⟩ := radialContact_spec ha hh
  obtain ⟨hv, hv', heqv⟩ := radialContact_spec (ha.trans hab) hh
  by_contra hn
  have huv : radialContact a h ≤ radialContact b h := le_of_not_gt hn
  have hH := H_strictMonoOn.monotoneOn ⟨hu.le, hu'.le⟩ ⟨hv.le, hv'.le⟩ huv
  have hm := mul_le_mul_of_nonneg_left (show 1 - 2 * radialContact b h ≤
      1 - 2 * radialContact a h by linarith) hh.le
  have hg : a * H (radialContact a h) < b * H (radialContact b h) := by
    calc
      a * H (radialContact a h) ≤ a * H (radialContact b h) :=
        mul_le_mul_of_nonneg_left hH ha.le
      _ < b * H (radialContact b h) :=
        mul_lt_mul_of_pos_right hab (H_pos hv (by linarith))
  linarith





theorem radialContact_normalize_entropy (z : ℝ) {h : ℝ} (hh : h ≠ 0) :
    radialContact z h = radialContact (z / h) 1 := by
  have hs := radialContact_scale z h (c := h⁻¹) (inv_ne_zero hh)
  simpa only [inv_mul_cancel₀ hh, ← div_eq_inv_mul] using hs.symm









end GeneralCK
end

section
namespace GeneralCK.Certificates.Reflection

























theorem biasE_eq_binEntropy {c : ℝ} (hc : -1 < c) (hc' : c < 1) :
    biasE c = Real.binEntropy ((1-c)/2) := by
  have hm : 0 < 1-c := by linarith
  have hp : 0 < 1+c := by linarith
  rw [Real.binEntropy]
  rw [Real.log_inv, Real.log_inv]
  rw [show 1-(1-c)/2 = (1+c)/2 by ring]
  rw [Real.log_div hm.ne' (by norm_num : (2:ℝ) ≠ 0),
      Real.log_div hp.ne' (by norm_num : (2:ℝ) ≠ 0)]
  unfold biasE
  ring







end GeneralCK.Certificates.Reflection
end

section
namespace GeneralCK.Certificates
open Set

/-- A second-derivative enclosure gives a lower Taylor bound along a segment. -/
theorem taylor_lower_of_second_bound {f df ddf : ℝ → ℝ} {M : ℝ}
    (hd : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt f (df t) t)
    (hdd : ∀ t ∈ Ioo (0:ℝ) 1, HasDerivAt df (ddf t) t)
    (hbound : ∀ t ∈ Ioo (0:ℝ) 1, -M ≤ ddf t) :
    f 0+df 0-M/2 ≤ f 1 := by
  let g : ℝ → ℝ := fun t => f t+(M/2)*t^2
  let dg : ℝ → ℝ := fun t => df t+M*t
  have hg : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt g (dg t) t := by
    intro t ht
    convert! (hd t ht).add (((hasDerivAt_id t).pow 2).const_mul (M/2)) using 1
    dsimp [dg]
    ring
  have hgg : ∀ t ∈ Ioo (0:ℝ) 1, HasDerivAt dg (ddf t+M) t := by
    intro t ht
    convert! (hdd t ht).add ((hasDerivAt_id t).const_mul M) using 1
    ring
  have hc : ConvexOn ℝ (Icc (0:ℝ) 1) g := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc 0 1)
      (fun t ht => (hg t ht).continuousAt.continuousWithinAt)
      (f' := dg) (f'' := fun t => ddf t+M)
    · intro t ht
      exact (hg t (interior_subset ht)).hasDerivWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact (hgg t ht).hasDerivWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      linarith [hbound t ht]
  have hb := hc.le_slope_of_hasDerivAt (by norm_num) (by norm_num) (by norm_num : (0:ℝ)<1)
    (hg 0 (by norm_num))
  dsimp [g,dg] at hb
  simp only [slope_def_field,zero_pow (by norm_num : 2 ≠ 0),one_pow,mul_zero,
    add_zero,sub_zero,div_one,mul_one] at hb
  linarith

/-- Certificate form of the one-variable Taylor estimate. -/
theorem taylor_lower_from_enclosures {f df ddf : ℝ → ℝ} {L A M : ℝ}
    (hd : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt f (df t) t)
    (hdd : ∀ t ∈ Ioo (0:ℝ) 1, HasDerivAt df (ddf t) t)
    (hvalue : L ≤ f 0) (hslope : -A ≤ df 0)
    (hbound : ∀ t ∈ Ioo (0:ℝ) 1, -M ≤ ddf t) :
    L-A-M/2 ≤ f 1 := by
  linarith [taylor_lower_of_second_bound hd hdd hbound]

/-- The bivariate Taylor remainder from componentwise second derivative bounds.
All second derivative bounds must hold throughout the segment. -/
theorem taylor_rectangle_lower {f df ddf haa haz hzz : ℝ → ℝ}
    {L pa pz Maa Maz Mzz ra rz da dz : ℝ}
    (hd : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt f (df t) t)
    (hdd : ∀ t ∈ Ioo (0:ℝ) 1, HasDerivAt df (ddf t) t)
    (hvalue : L ≤ f 0) (hslope : -(pa*ra+pz*rz) ≤ df 0)
    (hra : 0 ≤ ra) (_hrz : 0 ≤ rz) (hda : |da| ≤ ra) (hdz : |dz| ≤ rz)
    (hMaa : 0 ≤ Maa) (hMaz : 0 ≤ Maz) (hMzz : 0 ≤ Mzz)
    (hsecond : ∀ t ∈ Ioo (0:ℝ) 1, ddf t=haa t*da^2+2*haz t*da*dz+hzz t*dz^2)
    (haa_bound : ∀ t ∈ Ioo (0:ℝ) 1, |haa t| ≤ Maa)
    (haz_bound : ∀ t ∈ Ioo (0:ℝ) 1, |haz t| ≤ Maz)
    (hzz_bound : ∀ t ∈ Ioo (0:ℝ) 1, |hzz t| ≤ Mzz) :
    L-pa*ra-pz*rz-(Maa*ra^2+2*Maz*ra*rz+Mzz*rz^2)/2 ≤ f 1 := by
  have hda2 : da^2 ≤ ra^2 := by
    simpa only [← pow_two,sq_abs] using mul_self_le_mul_self (abs_nonneg da) hda
  have hdz2 : dz^2 ≤ rz^2 := by
    simpa only [← pow_two,sq_abs] using mul_self_le_mul_self (abs_nonneg dz) hdz
  have hcross : |da*dz| ≤ ra*rz := by
    rw [abs_mul]
    exact mul_le_mul hda hdz (abs_nonneg _) hra
  have hbound : ∀ t ∈ Ioo (0:ℝ) 1,
      -(Maa*ra^2+2*Maz*ra*rz+Mzz*rz^2) ≤ ddf t := by
    intro t ht
    have ha := (abs_le.mp (haa_bound t ht)).1
    have hz := (abs_le.mp (hzz_bound t ht)).1
    have hac := mul_le_mul_of_nonneg_right ha (sq_nonneg da)
    have hzc := mul_le_mul_of_nonneg_right hz (sq_nonneg dz)
    have har := mul_le_mul_of_nonneg_left hda2 hMaa
    have hzr := mul_le_mul_of_nonneg_left hdz2 hMzz
    have hcz : |haz t*(da*dz)| ≤ Maz*(ra*rz) := by
      rw [abs_mul]
      exact mul_le_mul (haz_bound t ht) hcross (abs_nonneg _) hMaz
    have hcl := (abs_le.mp hcz).1
    rw [hsecond t ht]
    nlinarith
  have hh := taylor_lower_from_enclosures hd hdd hvalue hslope hbound
  linarith



end GeneralCK.Certificates
end

section
namespace GeneralCK.Certificates

namespace DyadicInterval



theorem contains_toReal_iff {p : ℕ} {a : DyadicInterval p} {x : ℝ} :
    a.toReal.Contains x ↔ a.Contains x := by
  change (a.lo:ℝ)/(scale p:ℝ) ≤ x ∧ x ≤ (a.hi:ℝ)/(scale p:ℝ) ↔ _
  rw [div_le_iff₀ (scale_cast_pos p),le_div_iff₀ (scale_cast_pos p)]
  simp only [Contains,mul_comm]



end DyadicInterval



namespace DyadicJetEnclosure
open DyadicInterval





















theorem contains_variable {p : ℕ} {i : DyadicInterval p} {t : ℝ} (ht : i.Contains t) :
    (variableJet i).Contains Jet2.variableJet t :=
  ⟨ht,by simpa [variableJet,Jet2.variableJet] using ofInt_sound p 1,
    by simpa [variableJet,Jet2.variableJet] using ofInt_sound p 0⟩







theorem Contains.inv {p : ℕ} {b : DyadicJetEnclosure p} {j : Jet2} {t : ℝ}
    (hj : b.Contains j t) (hb : 0 < b.value.lo) : b.inv.Contains j.inv t := by
  have hr := recip_sound hb hj.1
  have hr2 := mul_sound hr hr
  have hr3 := mul_sound hr2 hr
  have htwo : (ofInt p 2).Contains (2:ℝ) := by simpa using ofInt_sound p 2
  refine ⟨hr,?_,?_⟩
  · simpa only [DyadicJetEnclosure.inv,Jet2.inv,div_eq_mul_inv,pow_two,mul_inv_rev] using
      mul_sound (neg_sound hj.2.1) hr2
  · convert! sub_sound (mul_sound (mul_sound htwo (mul_sound hj.2.1 hj.2.1)) hr3)
      (mul_sound hj.2.2 hr2) using 1
    simp only [Jet2.inv,div_eq_mul_inv]
    ring














end DyadicJetEnclosure
end GeneralCK.Certificates
end

section
namespace GeneralCK.Comparison
open Set









@[simp] theorem noiseParameter_zero (eps : ℝ) : noiseParameter eps 0 = eps := by
  simp [noiseParameter]



theorem hasDerivAt_H {p : ℝ} (hp : 0 < p) (hp' : p < 1) :
    HasDerivAt H (J p) p := by
  have hl : Real.log ((1 - p) / p) = Real.log (1 - p) - Real.log p :=
    Real.log_div (by linarith) (ne_of_gt hp)
  simpa [H, J, hl] using!
    (Real.hasDerivAt_binEntropy (ne_of_gt hp) (by linarith)).div_const (Real.log 2)







end GeneralCK.Comparison
end

section
namespace GeneralCK
open Set Filter
open scoped Topology

theorem radialContact_image_radius {h : ℝ} (hh : 0 < h) :
    (fun z => radialContact z h) '' Ioi 0 = Ioo 0 (1 / 2) := by
  ext v
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨radialContact_pos hz hh, radialContact_lt_half hz hh⟩
  · intro hv
    have hH : 0 < H v := H_pos hv.1 (by linarith [hv.2])
    have hz : 0 < h * (1 - 2 * v) / H v :=
      div_pos (mul_pos hh (by linarith [hv.2])) hH
    refine ⟨h * (1 - 2 * v) / H v, hz, ?_⟩
    apply radialContact_eq_of_equation hz hh hv.1 hv.2
    exact div_mul_cancel₀ _ hH.ne'

theorem continuousAt_radialContact_radius {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    ContinuousAt (fun r => radialContact r h) z := by
  have hanti : StrictAntiOn (fun r => radialContact r h) (Ioi 0) :=
    fun a ha b _ hab => radialContact_strictAnti_radius ha hab hh
  apply hanti.dual_right.continuousAt_of_image_mem_nhds (Ioi_mem_nhds hz)
  change (fun r => radialContact r h) '' Ioi 0 ∈ 𝓝 (radialContact z h)
  rw [radialContact_image_radius hh]
  exact Ioo_mem_nhds (radialContact_pos hz hh) (radialContact_lt_half hz hh)











namespace Certificates.Mixed











end Certificates.Mixed

open Certificates.Mixed















end GeneralCK
end

section
namespace GeneralCK.SmallMean
open Set





@[simp] theorem Cn_zero : Cn 0 = 0 := by norm_num [Cn]
@[simp] theorem Cn_one : Cn 1 = Real.log 2 := by norm_num [Cn]
@[simp] theorem A_zero : A 0 = 0 := by norm_num [A]



theorem A_eq_J (r : ℝ) : A r = Real.log 2 / 2 * J ((1-r)/2) := by
  have he : (1 - (1-r)/2) / ((1-r)/2) = (1+r)/(1-r) := by
    by_cases hr : r = 1
    · subst r; norm_num
    · field_simp [show 1-r ≠ 0 by exact sub_ne_zero.mpr (Ne.symm hr)]
      ring
  unfold A J
  rw [he]
  field_simp [log_two_pos.ne']





















end GeneralCK.SmallMean
end

section
namespace GeneralCK.Reflection
open Set Filter
open scoped Topology









theorem hasDerivAt_E {a : ℝ} (ha : -1 < a) (ha' : a < 1) :
    HasDerivAt E (-SmallMean.A a/Real.log 2) a := by
  have h := ((Comparison.hasDerivAt_H (p := (1-a)/2) (by linarith) (by linarith)).comp a
    (((hasDerivAt_id a).const_sub 1).div_const 2))
  convert! h using 1
  rw [SmallMean.A_eq_J]
  field_simp





@[simp] theorem D_zero (a : ℝ) : D a 0 = 0 := by simp [D]











@[simp] theorem curvature_zero (a : ℝ) : curvature a 0 = 0 := by simp [curvature]

















end GeneralCK.Reflection
end

section
namespace GeneralCK.Reflection
open Certificates.Reflection Set Filter
open scoped Topology






theorem biasE_eq_log_mul_E {c : ℝ} (hc : -1 < c) (hc' : c < 1) :
    biasE c = Real.log 2*E c := by
  rw [biasE_eq_binEntropy hc hc']
  unfold E H
  field_simp

theorem hasDerivAt_biasE {c : ℝ} (hc : -1 < c) (hc' : c < 1) :
    HasDerivAt biasE (-SmallMean.A c) c := by
  have hd := (hasDerivAt_E hc hc').const_mul (Real.log 2)
  have heq : biasE =ᶠ[𝓝 c] (fun t => Real.log 2*E t) := by
    filter_upwards [Ioo_mem_nhds hc hc'] with t ht
    exact biasE_eq_log_mul_E ht.1 ht.2
  convert! hd.congr_of_eventuallyEq heq using 1
  field_simp

theorem hasDerivAt_biasB {c : ℝ} (hc : -1 < c) (hc' : c < 1) :
    HasDerivAt biasB (c/(1-c^2)) c := by
  have hn : 1-c^2 ≠ 0 := by nlinarith
  have hd := ((((hasDerivAt_id c).pow 2).const_sub 1).log hn).div_const 2
  convert! hd.const_sub (Real.log 2) using 1
  · funext t; simp only [biasB,pow_two,Pi.mul_apply,id_eq]
  · simp only [Pi.pow_apply,id_eq]
    field_simp; ring

theorem biasB_eq_biasE_add {c : ℝ} (hc : -1 < c) (hc' : c < 1) :
    biasB c = biasE c+c*SmallMean.A c := by
  have hm : 1-c ≠ 0 := by linarith
  have hp : 1+c ≠ 0 := by linarith
  unfold biasB biasE SmallMean.A
  rw [show 1-c*c=(1+c)*(1-c) by ring,Real.log_mul hp hm,Real.log_div hp hm]
  ring

theorem hasDerivAt_biasR {c : ℝ} (hc : 0 < c) (hc' : c < 1) :
    HasDerivAt biasR (biasRprime c) c := by
  have hd := (hasDerivAt_biasE (by linarith) hc').div (hasDerivAt_id c) hc.ne'
  convert! hd using 1
  rw [biasRprime,biasB_eq_biasE_add (by linarith) hc']
  simp only [id_eq]
  ring

theorem hasDerivAt_biasRprime {c : ℝ} (hc : 0 < c) (hc' : c < 1) :
    HasDerivAt biasRprime (biasRsecond c) c := by
  have hd := (hasDerivAt_biasB (by linarith) hc').neg.div
    ((hasDerivAt_id c).pow 2) (pow_ne_zero 2 hc.ne')
  convert! hd using 1
  unfold biasRsecond
  simp only [Pi.pow_apply,Pi.neg_apply,id_eq]
  field_simp [hc.ne',show 1-c^2 ≠ 0 by nlinarith]
  ring

theorem biasContact_mem {y : ℝ} (hy : 0 < y) : biasContact y ∈ Ioo (0:ℝ) 1 := by
  have hh := div_pos hy log_two_pos
  have hv := radialContact_pos (by norm_num : (0:ℝ)<1) hh
  have hv' := radialContact_lt_half (by norm_num : (0:ℝ)<1) hh
  unfold biasContact
  constructor <;> linarith

theorem biasR_biasContact {y : ℝ} (hy : 0 < y) : biasR (biasContact y)=y := by
  have hc := biasContact_mem hy
  rw [biasR,biasE_eq_log_mul_E (by linarith [hc.1]) hc.2]
  unfold E biasContact
  rw [show (1-(1-2*radialContact 1 (y/Real.log 2)))/2=radialContact 1 (y/Real.log 2) by ring]
  have he := radialContact_equation (by norm_num : (0:ℝ)<1) (div_pos hy log_two_pos)
  apply (div_eq_iff (show 1-2*radialContact 1 (y/Real.log 2) ≠ 0 from hc.1.ne')).mpr
  field_simp at he
  nlinarith

theorem continuousAt_biasContact {y : ℝ} (hy : 0 < y) : ContinuousAt biasContact y := by
  have ht : ContinuousAt (fun t : ℝ => Real.log 2/t) y := continuousAt_const.div continuousAt_id hy.ne'
  have hc := (continuousAt_radialContact_radius (div_pos log_two_pos hy) (by norm_num : (0:ℝ)<1)).comp ht
  have heq : biasContact =ᶠ[𝓝 y] (fun t => 1-2*radialContact (Real.log 2/t) 1) := by
    filter_upwards [Ioi_mem_nhds hy] with t ht
    unfold biasContact
    rw [radialContact_normalize_entropy 1 (div_pos (show 0<t from ht) log_two_pos).ne']
    simp only [one_div,inv_div]
  exact (continuousAt_const.sub (continuousAt_const.mul hc)).congr_of_eventuallyEq heq

theorem biasB_pos {c : ℝ} (hc : 0 < c) (hc' : c < 1) : 0 < biasB c := by
  have hlog : Real.log (1-c*c) ≤ 0 := Real.log_nonpos (by nlinarith) (by nlinarith)
  unfold biasB
  linarith [log_two_pos]

theorem hasDerivAt_biasContact {y : ℝ} (hy : 0 < y) :
    HasDerivAt biasContact (-(biasContact y)^2/biasB (biasContact y)) y := by
  have hc := biasContact_mem hy
  have hk := (biasB_pos hc.1 hc.2).ne'
  have hd := (hasDerivAt_biasR hc.1 hc.2).of_local_left_inverse (continuousAt_biasContact hy)
    (show biasRprime (biasContact y) ≠ 0 from div_ne_zero (neg_ne_zero.mpr hk) (pow_ne_zero 2 hc.1.ne')) (by
      filter_upwards [Ioi_mem_nhds hy] with t ht
      exact biasR_biasContact ht)
  convert! hd using 1
  unfold biasRprime
  rw [inv_div,div_neg,neg_div]

theorem hasDerivAt_biasContact_inv {y : ℝ} (hy : 0 < y) :
    HasDerivAt biasContact ((biasRprime (biasContact y))⁻¹) y := by
  convert! hasDerivAt_biasContact hy using 1
  unfold biasRprime
  rw [inv_div,div_neg,neg_div]

theorem hasDerivAt_deriv_biasContact {y : ℝ} (hy : 0 < y) :
    HasDerivAt (deriv biasContact)
      (-biasRsecond (biasContact y)/(biasRprime (biasContact y))^3) y := by
  have hc := biasContact_mem hy
  have hn : biasRprime (biasContact y) ≠ 0 :=
    div_ne_zero (neg_ne_zero.mpr (biasB_pos hc.1 hc.2).ne') (pow_ne_zero 2 hc.1.ne')
  have hd := ((hasDerivAt_biasRprime hc.1 hc.2).comp y (hasDerivAt_biasContact_inv hy)).inv hn
  have heq : deriv biasContact =ᶠ[𝓝 y] (fun t => (biasRprime (biasContact t))⁻¹) := by
    filter_upwards [Ioi_mem_nhds hy] with t ht
    exact (hasDerivAt_biasContact_inv ht).deriv
  convert! hd.congr_of_eventuallyEq heq using 1
  simp only [Function.comp_apply]
  field_simp [hn]



end GeneralCK.Reflection
end

section
namespace GeneralCK.Certificates
open Set Filter
open scoped Topology



theorem reflectionContactJet_soundAt {y : ℝ} (hy : 0 < y) :
    reflectionContactJet.SoundAt y := by
  refine ⟨Reflection.hasDerivAt_biasContact_inv hy, ?_⟩
  have heq : reflectionContactJet.first =ᶠ[𝓝 y] deriv Reflection.biasContact := by
    filter_upwards [Ioi_mem_nhds hy] with t ht
    exact (Reflection.hasDerivAt_biasContact_inv ht).deriv.symm
  exact (Reflection.hasDerivAt_deriv_biasContact hy).congr_of_eventuallyEq heq







end GeneralCK.Certificates
end

section
namespace GeneralCK.Certificates



namespace BivariateJet2
























private theorem jet_ext {j k : Jet2} (hv : j.value=k.value)
    (hf : j.first=k.first) (hs : j.second=k.second) : j=k := by
  cases j; cases k; simp_all

private theorem biv_ext {j k : BivariateJet2} (hv : j.value=k.value)
    (ha : j.firstA=k.firstA) (hz : j.firstZ=k.firstZ)
    (haa : j.secondAA=k.secondAA) (haz : j.secondAZ=k.secondAZ)
    (hzz : j.secondZZ=k.secondZZ) : j=k := by
  cases j; cases k; simp_all

theorem inv_eq_outerCompose (j : BivariateJet2) :
    j.inv=outerCompose Jet2.variableJet.inv j := by
  apply biv_ext <;> funext t <;>
    simp only [inv,outerCompose,Jet2.inv,Jet2.variableJet,id_eq,div_eq_mul_inv] <;> ring

theorem log_eq_outerCompose (j : BivariateJet2) :
    j.log=outerCompose Jet2.variableJet.log j := by
  apply biv_ext <;> funext t <;>
    simp only [log,outerCompose,Jet2.log,Jet2.variableJet,id_eq,div_eq_mul_inv] <;> ring

@[simp] theorem projection_const (c da dz : ℝ) :
    (const c).projection da dz=Jet2.const c := by
  apply jet_ext <;> funext t <;> simp [projection,const,Jet2.const]

@[simp] theorem projection_affineA (c x dz : ℝ) :
    (affineA c x).projection (x-c) dz=Jet2.segment c x := by
  apply jet_ext <;> funext t <;> simp [projection,affineA,coordinateA,Jet2.segment]

@[simp] theorem projection_affineZ (c x da : ℝ) :
    (affineZ c x).projection da (x-c)=Jet2.segment c x := by
  apply jet_ext <;> funext t <;> simp [projection,affineZ,coordinateZ,Jet2.segment]

@[simp] theorem projection_add (j k : BivariateJet2) (da dz : ℝ) :
    (j.add k).projection da dz=(j.projection da dz).add (k.projection da dz) := by
  apply jet_ext <;> funext t <;> simp only [projection,add,Jet2.add] <;> ring

@[simp] theorem projection_neg (j : BivariateJet2) (da dz : ℝ) :
    j.neg.projection da dz=(j.projection da dz).neg := by
  apply jet_ext <;> funext t <;> simp only [projection,neg,Jet2.neg] <;> ring

@[simp] theorem projection_mul (j k : BivariateJet2) (da dz : ℝ) :
    (j.mul k).projection da dz=(j.projection da dz).mul (k.projection da dz) := by
  apply jet_ext <;> funext t <;> simp only [projection,mul,Jet2.mul] <;> ring

/-- Algebraic commutation is unconditional, including the totalized zero inverse.
Actual derivative soundness still requires the usual nonzero hypothesis. -/
@[simp] theorem projection_inv (j : BivariateJet2) (da dz : ℝ) :
    j.inv.projection da dz=(j.projection da dz).inv := by
  apply jet_ext <;> funext t <;> simp only [projection,inv,Jet2.inv,div_eq_mul_inv] <;> ring

@[simp] theorem projection_log (j : BivariateJet2) (da dz : ℝ) :
    j.log.projection da dz=(j.projection da dz).log := by
  apply jet_ext <;> funext t <;> simp only [projection,log,Jet2.log,div_eq_mul_inv] <;> ring

@[simp] theorem projection_outerCompose (outer : Jet2) (j : BivariateJet2) (da dz : ℝ) :
    (outerCompose outer j).projection da dz=outer.comp (j.projection da dz) := by
  apply jet_ext <;> funext t <;> simp only [projection,outerCompose,Jet2.comp] <;> ring





theorem DirectionalSoundAt.add {j k : BivariateJet2} {da dz t : ℝ}
    (hj : j.DirectionalSoundAt da dz t) (hk : k.DirectionalSoundAt da dz t) :
    (j.add k).DirectionalSoundAt da dz t := by
  simpa only [DirectionalSoundAt,projection_add] using Jet2.SoundAt.add hj hk

theorem DirectionalSoundAt.neg {j : BivariateJet2} {da dz t : ℝ}
    (hj : j.DirectionalSoundAt da dz t) : j.neg.DirectionalSoundAt da dz t := by
  simpa only [DirectionalSoundAt,projection_neg] using Jet2.SoundAt.neg hj

theorem DirectionalSoundAt.mul {j k : BivariateJet2} {da dz t : ℝ}
    (hj : j.DirectionalSoundAt da dz t) (hk : k.DirectionalSoundAt da dz t) :
    (j.mul k).DirectionalSoundAt da dz t := by
  simpa only [DirectionalSoundAt,projection_mul] using Jet2.SoundAt.mul hj hk

theorem DirectionalSoundAt.inv {j : BivariateJet2} {da dz t : ℝ}
    (hj : j.DirectionalSoundAt da dz t) (hn : j.value t≠0) :
    j.inv.DirectionalSoundAt da dz t := by
  simpa only [DirectionalSoundAt,projection_inv] using Jet2.SoundAt.inv hj hn

theorem DirectionalSoundAt.log {j : BivariateJet2} {da dz t : ℝ}
    (hj : j.DirectionalSoundAt da dz t) (hn : j.value t≠0) :
    j.log.DirectionalSoundAt da dz t := by
  simpa only [DirectionalSoundAt,projection_log] using Jet2.SoundAt.log hj hn

theorem DirectionalSoundAt.outerCompose {outer : Jet2} {j : BivariateJet2} {da dz t : ℝ}
    (ho : outer.SoundAt (j.value t)) (hj : j.DirectionalSoundAt da dz t) :
    (outerCompose outer j).DirectionalSoundAt da dz t := by
  simpa only [DirectionalSoundAt,projection_outerCompose] using ho.comp hj







end BivariateJet2
end GeneralCK.Certificates
end

section
namespace GeneralCK.Certificates
open DyadicInterval

namespace DyadicInterval.Contains

theorem add {p : ℕ} {a b : DyadicInterval p} {x y : ℝ} (hx : a.Contains x) (hy : b.Contains y) :
    (a.add b).Contains (x+y) := add_sound hx hy

theorem neg {p : ℕ} {a : DyadicInterval p} {x : ℝ} (hx : a.Contains x) :
    a.neg.Contains (-x) := neg_sound hx

theorem mul {p : ℕ} {a b : DyadicInterval p} {x y : ℝ} (hx : a.Contains x) (hy : b.Contains y) :
    (a.mul b).Contains (x*y) := mul_sound hx hy

end DyadicInterval.Contains



namespace DyadicBivariateJetEnclosure
variable {p : ℕ}








theorem contains_toReal_iff {b : DyadicBivariateJetEnclosure p} {j : BivariateJet2} {t : ℝ} :
    b.toReal.Contains j t ↔ b.Contains j t := by
  simp only [toReal,BivariateJetEnclosure.Contains,Contains,DyadicInterval.contains_toReal_iff]

theorem containsOn_toReal_iff {b : DyadicBivariateJetEnclosure p} {j : BivariateJet2} {s : Set ℝ} :
    b.toReal.ContainsOn j s ↔ b.ContainsOn j s := by
  simp only [BivariateJetEnclosure.ContainsOn,ContainsOn,contains_toReal_iff]





















theorem Contains.add {b c : DyadicBivariateJetEnclosure p} {j k : BivariateJet2} {t : ℝ}
    (hj : b.Contains j t) (hk : c.Contains k t) : (b.add c).Contains (j.add k) t :=
  ⟨hj.1.add hk.1,hj.2.1.add hk.2.1,hj.2.2.1.add hk.2.2.1,
    hj.2.2.2.1.add hk.2.2.2.1,hj.2.2.2.2.1.add hk.2.2.2.2.1,
    hj.2.2.2.2.2.add hk.2.2.2.2.2⟩

theorem Contains.neg {b : DyadicBivariateJetEnclosure p} {j : BivariateJet2} {t : ℝ}
    (hj : b.Contains j t) : b.neg.Contains j.neg t :=
  ⟨hj.1.neg,hj.2.1.neg,hj.2.2.1.neg,hj.2.2.2.1.neg,hj.2.2.2.2.1.neg,hj.2.2.2.2.2.neg⟩

theorem Contains.mul {b c : DyadicBivariateJetEnclosure p} {j k : BivariateJet2} {t : ℝ}
    (hj : b.Contains j t) (hk : c.Contains k t) : (b.mul c).Contains (j.mul k) t := by
  have htwo : (ofInt p 2).Contains (2:ℝ) := by simpa using ofInt_sound p 2
  exact ⟨hj.1.mul hk.1,(hj.2.1.mul hk.1).add (hj.1.mul hk.2.1),
    (hj.2.2.1.mul hk.1).add (hj.1.mul hk.2.2.1),
    ((hj.2.2.2.1.mul hk.1).add ((htwo.mul hj.2.1).mul hk.2.1)).add (hj.1.mul hk.2.2.2.1),
    (((hj.2.2.2.2.1.mul hk.1).add (hj.2.1.mul hk.2.2.1)).add
      (hj.2.2.1.mul hk.2.1)).add (hj.1.mul hk.2.2.2.2.1),
    ((hj.2.2.2.2.2.mul hk.1).add ((htwo.mul hj.2.2.1).mul hk.2.2.1)).add
      (hj.1.mul hk.2.2.2.2.2)⟩

theorem Contains.outerCompose {outer : DyadicJetEnclosure p} {b : DyadicBivariateJetEnclosure p}
    {f : Jet2} {j : BivariateJet2} {t : ℝ} (hf : outer.Contains f (j.value t))
    (hj : b.Contains j t) : (outerCompose outer b).Contains (BivariateJet2.outerCompose f j) t := by
  exact ⟨hf.1,hf.2.1.mul hj.2.1,hf.2.1.mul hj.2.2.1,
    by simpa only [DyadicBivariateJetEnclosure.outerCompose,BivariateJet2.outerCompose,pow_two,mul_assoc] using
      ((hf.2.2.mul hj.2.1).mul hj.2.1).add (hf.2.1.mul hj.2.2.2.1),
    ((hf.2.2.mul hj.2.1).mul hj.2.2.1).add (hf.2.1.mul hj.2.2.2.2.1),
    by simpa only [DyadicBivariateJetEnclosure.outerCompose,BivariateJet2.outerCompose,pow_two,mul_assoc] using
      ((hf.2.2.mul hj.2.2.1).mul hj.2.2.1).add (hf.2.1.mul hj.2.2.2.2.2)⟩



theorem subsetCheck_sound {b out : DyadicBivariateJetEnclosure p} {j : BivariateJet2} {t : ℝ}
    (h : b.subsetCheck out=true) (hj : b.Contains j t) : out.Contains j t := by
  simp only [subsetCheck,Bool.and_eq_true_iff] at h
  exact ⟨DyadicInterval.subsetCheck_sound h.1.1.1.1.1 hj.1,
    DyadicInterval.subsetCheck_sound h.1.1.1.1.2 hj.2.1,
    DyadicInterval.subsetCheck_sound h.1.1.1.2 hj.2.2.1,
    DyadicInterval.subsetCheck_sound h.1.1.2 hj.2.2.2.1,
    DyadicInterval.subsetCheck_sound h.1.2 hj.2.2.2.2.1,
    DyadicInterval.subsetCheck_sound h.2 hj.2.2.2.2.2⟩



theorem Contains.inv {b : DyadicBivariateJetEnclosure p} {j : BivariateJet2} {t : ℝ}
    (hj : b.Contains j t) (hpos : 0<b.value.lo) :
    b.inv.Contains (BivariateJet2.outerCompose Jet2.variableJet.inv j) t :=
  Contains.outerCompose (DyadicJetEnclosure.Contains.inv (DyadicJetEnclosure.contains_variable hj.1) hpos) hj



theorem invCheck_positive {b out : DyadicBivariateJetEnclosure p} (h : invCheck b out=true) :
    0<b.value.lo := of_decide_eq_true (Bool.and_eq_true_iff.mp h).1

theorem invCheck_sound {b out : DyadicBivariateJetEnclosure p} {j : BivariateJet2} {t : ℝ}
    (h : invCheck b out=true) (hj : b.Contains j t) :
    out.Contains (BivariateJet2.outerCompose Jet2.variableJet.inv j) t := by
  have hh := Bool.and_eq_true_iff.mp h
  exact subsetCheck_sound hh.2 (hj.inv (of_decide_eq_true hh.1))

















end DyadicBivariateJetEnclosure
end GeneralCK.Certificates
end

section
namespace GeneralCK.Certificates.BivariateJetProgram










namespace Op













end Op



























theorem RegistersContain.cons {p : ℕ} {boxes : List (DyadicBivariateJetEnclosure p)} {jets : List BivariateJet2}
    {t : ℝ} {box : DyadicBivariateJetEnclosure p} {jet : BivariateJet2} (h : RegistersContain boxes jets t)
    (hj : box.Contains jet t) : RegistersContain (box::boxes) (jet::jets) t := by
  refine ⟨by simpa using h.1,?_⟩
  intro i
  cases i with
  | zero => simpa using hj
  | succ i => simpa using h.2 i

theorem RegistersSound.cons {jets : List BivariateJet2} {jet : BivariateJet2} {da dz t : ℝ}
    (h : RegistersSound jets da dz t) (hj : jet.DirectionalSoundAt da dz t) :
    RegistersSound (jet::jets) da dz t := by
  intro i
  cases i with
  | zero => simpa using hj
  | succ i => simpa using h i



























end GeneralCK.Certificates.BivariateJetProgram
end

section
namespace GeneralCK.Certificates
open Set JetBounds

namespace JetBounds.Interval



theorem magnitude_nonneg (i : Interval) : 0 ≤ i.magnitude :=
  (abs_nonneg i.lo).trans (le_max_left _ _)

theorem Contains.abs_le_magnitude {i : Interval} {x : ℝ} (hx : i.Contains x) :
    |x| ≤ i.magnitude := by
  apply abs_le.mpr
  constructor
  · exact (neg_le_neg (le_max_left _ _)).trans ((neg_abs_le i.lo).trans hx.1)
  · exact hx.2.trans ((le_abs_self i.hi).trans (le_max_right _ _))

end JetBounds.Interval

namespace BivariateJetEnclosure



theorem taylor_lower {center whole : BivariateJetEnclosure} {j : BivariateJet2}
    {da dz ra rz : ℝ}
    (hs : j.DirectionalSoundOn da dz (Icc (0:ℝ) 1))
    (hc : center.Contains j 0) (hw : whole.ContainsOn j (Icc (0:ℝ) 1))
    (hra : 0≤ra) (hrz : 0≤rz) (hda : |da|≤ra) (hdz : |dz|≤rz) :
    taylorLower center whole ra rz≤j.value 1 := by
  have hA := hc.2.1.abs_le_magnitude
  have hZ := hc.2.2.1.abs_le_magnitude
  have hAterm : |j.firstA 0*da|≤center.firstA.magnitude*ra := by
    rw [abs_mul]
    exact mul_le_mul hA hda (abs_nonneg _) center.firstA.magnitude_nonneg
  have hZterm : |j.firstZ 0*dz|≤center.firstZ.magnitude*rz := by
    rw [abs_mul]
    exact mul_le_mul hZ hdz (abs_nonneg _) center.firstZ.magnitude_nonneg
  have hslope : -(center.firstA.magnitude*ra+center.firstZ.magnitude*rz)≤
      (j.projection da dz).first 0 := by
    have h := (abs_add_le (j.firstA 0*da) (j.firstZ 0*dz)).trans (add_le_add hAterm hZterm)
    exact (abs_le.mp h).1
  exact taylor_rectangle_lower
    (fun t ht => (hs t ht).1)
    (fun t ht => (hs t ⟨ht.1.le,ht.2.le⟩).2)
    hc.1.1 hslope hra hrz hda hdz
    whole.secondAA.magnitude_nonneg whole.secondAZ.magnitude_nonneg whole.secondZZ.magnitude_nonneg
    (fun _ _ => rfl)
    (fun t ht => (hw t ⟨ht.1.le,ht.2.le⟩).2.2.2.1.abs_le_magnitude)
    (fun t ht => (hw t ⟨ht.1.le,ht.2.le⟩).2.2.2.2.1.abs_le_magnitude)
    (fun t ht => (hw t ⟨ht.1.le,ht.2.le⟩).2.2.2.2.2.abs_le_magnitude)

theorem value_pos_of_taylor {center whole : BivariateJetEnclosure} {j : BivariateJet2}
    {da dz ra rz : ℝ}
    (hs : j.DirectionalSoundOn da dz (Icc (0:ℝ) 1))
    (hc : center.Contains j 0) (hw : whole.ContainsOn j (Icc (0:ℝ) 1))
    (hra : 0≤ra) (hrz : 0≤rz) (hda : |da|≤ra) (hdz : |dz|≤rz)
    (hcheck : 0<taylorLower center whole ra rz) : 0<j.value 1 :=
  hcheck.trans_le (taylor_lower hs hc hw hra hrz hda hdz)

end BivariateJetEnclosure
end GeneralCK.Certificates
end

section
namespace GeneralCK.Certificates
open Set

namespace DyadicBivariateJetEnclosure









/-- Convert separately checked coordinate enclosures to the real Taylor rule.
The center and uniform enclosures may use different dyadic precisions. -/
theorem value_pos_of_separate_taylor {p q : ℕ}
    {center : DyadicBivariateJetEnclosure p} {whole : DyadicBivariateJetEnclosure q}
    {j : BivariateJet2} {da dz ra rz : ℝ}
    (hs : j.DirectionalSoundOn da dz (Icc (0:ℝ) 1))
    (hc : center.Contains j 0) (hw : whole.ContainsOn j (Icc (0:ℝ) 1))
    (hra : 0≤ra) (hrz : 0≤rz) (hda : |da|≤ra) (hdz : |dz|≤rz)
    (ht : 0<BivariateJetEnclosure.taylorLower center.toReal whole.toReal ra rz) :
    0<j.value 1 :=
  BivariateJetEnclosure.value_pos_of_taylor hs (contains_toReal_iff.mpr hc)
    (containsOn_toReal_iff.mpr hw) hra hrz hda hdz ht

end DyadicBivariateJetEnclosure

namespace BivariateJetProgram



end BivariateJetProgram
end GeneralCK.Certificates
end

section
namespace GeneralCK.Certificates.ProvedTranscendental
open DyadicInterval GeneralCK.Reflection GeneralCK.Certificates.Reflection





theorem jetLog_sound {p : ℕ} {b : DyadicJetEnclosure p} {out : DyadicInterval p}
    {j : Jet2} {t : ℝ} (hb : b.Contains j t) (hp : 0<b.value.lo)
    (hv : out.Contains (Real.log (j.value t))) :
    (DyadicLog.jetLog b out).Contains j.log t := by
  have hr := recip_sound hp hb.1
  refine ⟨hv,?_,?_⟩
  · simpa only [DyadicLog.jetLog,Jet2.log,div_eq_mul_inv] using mul_sound hb.2.1 hr
  · convert! sub_sound (mul_sound hb.2.2 hr)
      (mul_sound (mul_sound hb.2.1 hb.2.1) (mul_sound hr hr)) using 1
    simp only [Jet2.log,div_eq_mul_inv]
    ring

theorem bivariateLog_sound {p : ℕ} {b : DyadicBivariateJetEnclosure p}
    {out : DyadicInterval p} {j : BivariateJet2} {t : ℝ}
    (hb : b.Contains j t) (hp : 0<b.value.lo) (hl : LogEncloses b.value out) :
    (b.log out).Contains (BivariateJet2.outerCompose Jet2.variableJet.log j) t :=
  DyadicBivariateJetEnclosure.Contains.outerCompose
    (jetLog_sound (DyadicJetEnclosure.contains_variable hb.1) hp (hl _ hb.1)) hb













end GeneralCK.Certificates.ProvedTranscendental
end

section
namespace GeneralCK.Certificates.BivariateProvedProgram
open BivariateJetProgram Set

















theorem finalJets_eq_executeShapes {p : ℕ} (program : List (Instruction p))
    (jets : List BivariateJet2) : finalJets program jets=executeShapes (shapes program) jets := by
  induction program generalizing jets with
  | nil => rfl
  | cons ins rest ih => simpa only [finalJets,shapes,List.map_cons,executeShapes] using ih (ins.shape.eval jets::jets)

theorem finalJets_eq_of_shapes_eq {p q : ℕ} {left : List (Instruction p)}
    {right : List (Instruction q)} (h : shapes left=shapes right) (jets : List BivariateJet2) :
    finalJets left jets=finalJets right jets := by
  rw [finalJets_eq_executeShapes,finalJets_eq_executeShapes,h]



theorem StepValid.encloses {p : ℕ} (shape : Shape)
    {boxes : List (DyadicBivariateJetEnclosure p)} {jets : List BivariateJet2}
    {out : DyadicBivariateJetEnclosure p} {t : ℝ}
    (h : RegistersContain boxes jets t) (hc : StepValid shape boxes out) :
    out.Contains (shape.eval jets) t := by
  have hd := hc.2
  cases shape with
  | add i j => exact DyadicBivariateJetEnclosure.subsetCheck_sound hd ((h.2 i).add (h.2 j))
  | neg i => exact DyadicBivariateJetEnclosure.subsetCheck_sound hd (h.2 i).neg
  | mul i j => exact DyadicBivariateJetEnclosure.subsetCheck_sound hd ((h.2 i).mul (h.2 j))
  | inv i => simpa only [Shape.eval,BivariateJet2.inv_eq_outerCompose] using
      DyadicBivariateJetEnclosure.invCheck_sound hd (h.2 i)
  | log i =>
    simpa only [Shape.eval,BivariateJet2.log_eq_outerCompose] using
      DyadicBivariateJetEnclosure.subsetCheck_sound hd.2.2
        (ProvedTranscendental.bivariateLog_sound (h.2 i) hd.1 hd.2.1)
  | contact i =>
    obtain ⟨outer,ho,hsub⟩ := hd.2
    exact DyadicBivariateJetEnclosure.subsetCheck_sound hsub
      (DyadicBivariateJetEnclosure.Contains.outerCompose (ho _ (h.2 i).1) (h.2 i))

theorem StepValid.soundAt {p : ℕ} (shape : Shape)
    {boxes : List (DyadicBivariateJetEnclosure p)} {jets : List BivariateJet2}
    {out : DyadicBivariateJetEnclosure p} {da dz t : ℝ}
    (h : RegistersContain boxes jets t) (hs : RegistersSound jets da dz t)
    (hc : StepValid shape boxes out) : (shape.eval jets).DirectionalSoundAt da dz t := by
  have hd := hc.2
  cases shape with
  | add i j => exact (hs i).add (hs j)
  | neg i => exact (hs i).neg
  | mul i j => exact (hs i).mul (hs j)
  | inv i =>
    have hp := DyadicBivariateJetEnclosure.invCheck_positive hd
    have hpos := DyadicInterval.positiveCheck_sound
      (by simpa [DyadicInterval.positiveCheck] using hp) (h.2 i).1
    exact (hs i).inv hpos.ne'
  | log i =>
    have hpos := DyadicInterval.positiveCheck_sound
      (by simpa [DyadicInterval.positiveCheck] using hd.1) (h.2 i).1
    exact (hs i).log hpos.ne'
  | contact i =>
    have hpos := DyadicInterval.positiveCheck_sound
      (by simpa [DyadicInterval.positiveCheck] using hd.1) (h.2 i).1
    exact BivariateJet2.DirectionalSoundAt.outerCompose (reflectionContactJet_soundAt hpos) (hs i)

theorem Accepted.encloses {p : ℕ} (program : List (Instruction p))
    {boxes : List (DyadicBivariateJetEnclosure p)} {jets : List BivariateJet2} {t : ℝ}
    (h : RegistersContain boxes jets t) (hc : Accepted program boxes) :
    RegistersContain (finalBoxes program boxes) (finalJets program jets) t := by
  induction program generalizing boxes jets with
  | nil => exact h
  | cons ins rest ih => exact ih (h.cons (StepValid.encloses ins.shape h hc.1)) hc.2

theorem Accepted.preserves_sound {p : ℕ} (program : List (Instruction p))
    {boxes : List (DyadicBivariateJetEnclosure p)} {jets : List BivariateJet2} {da dz t : ℝ}
    (h : RegistersContain boxes jets t) (hs : RegistersSound jets da dz t)
    (hc : Accepted program boxes) : RegistersSound (finalJets program jets) da dz t := by
  induction program generalizing boxes jets with
  | nil => exact hs
  | cons ins rest ih =>
    exact ih (h.cons (StepValid.encloses ins.shape h hc.1))
      (hs.cons (StepValid.soundAt ins.shape h hs hc.1)) hc.2

theorem Accepted.preserves_soundOn {p : ℕ} (program : List (Instruction p))
    {boxes : List (DyadicBivariateJetEnclosure p)} {jets : List BivariateJet2}
    {s : Set ℝ} {da dz : ℝ}
    (h : ∀ t ∈ s, RegistersContain boxes jets t)
    (hs : ∀ i, (jets.getD i zeroJet).DirectionalSoundOn da dz s)
    (hc : Accepted program boxes) :
    ∀ i, ((finalJets program jets).getD i zeroJet).DirectionalSoundOn da dz s :=
  fun i t ht => hc.preserves_sound program (h t ht) (fun i => hs i t ht) i















end GeneralCK.Certificates.BivariateProvedProgram
end

open GeneralCK GeneralCK.Certificates GeneralCK.Certificates.BivariateProvedProgram
open BivariateJetProgram Set
theorem solution {p q : ℕ}
    (center : List (_root_.GeneralCK.Certificates.BivariateProvedProgram.Instruction p)) (whole : List (_root_.GeneralCK.Certificates.BivariateProvedProgram.Instruction q))
    {centerInputs : List (DyadicBivariateJetEnclosure p)}
    {wholeInputs : List (DyadicBivariateJetEnclosure q)} {jets : List BivariateJet2}
    (i : ℕ) {da dz ra rz : ℝ}
    (hshape : shapes center=shapes whole)
    (hc : RegistersContain centerInputs jets 0)
    (hw : ∀ t ∈ Icc (0:ℝ) 1, RegistersContain wholeInputs jets t)
    (hs : ∀ i, (jets.getD i zeroJet).DirectionalSoundOn da dz (Icc (0:ℝ) 1))
    (hcc : Accepted center centerInputs) (hwc : Accepted whole wholeInputs)
    (hra : 0≤ra) (hrz : 0≤rz) (hda : |da|≤ra) (hdz : |dz|≤rz)
    (ht : 0<BivariateJetEnclosure.taylorLower
      ((finalBoxes center centerInputs).getD i (zeroBox p)).toReal
      ((finalBoxes whole wholeInputs).getD i (zeroBox q)).toReal ra rz) :
    0<((finalJets whole jets).getD i zeroJet).value 1 := by
  have heq := finalJets_eq_of_shapes_eq hshape jets
  have hcenter := (Accepted.encloses center hc hcc).2 i
  rw [heq] at hcenter
  exact DyadicBivariateJetEnclosure.value_pos_of_separate_taylor
    (Accepted.preserves_soundOn whole hw hs hwc i) hcenter
    (fun t ht => (Accepted.encloses whole (hw t ht) hwc).2 i) hra hrz hda hdz ht
