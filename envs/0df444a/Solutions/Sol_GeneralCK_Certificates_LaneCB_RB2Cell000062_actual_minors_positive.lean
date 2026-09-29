-- Prove2me | solution 1 for GeneralCK.Certificates.LaneCB.RB2Cell000062.actual_minors_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-25T17:30:41.407919+00:00
-- url     : https://prove2.me/submissions/559a6ac9-8a44-423d-baa7-34ddcef480a0

import Definitions.Def_GeneralCK_E8_interval_checkers
import Definitions.Def_GeneralCK_E8_semantic_core
import Definitions.Def_GeneralCK_RB2_checker_semantics_v2
import Definitions.Def_GeneralCK_RB2_program_data
import Definitions.Def_GeneralCK_bellman
import Definitions.Def_GeneralCK_correction_minors
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
import Theorems.Thm_GeneralCK_Certificates_BivariateProvedProgram_value_pos_of_accepted_taylor
import Theorems.Thm_GeneralCK_Certificates_CorrectionFactorizedProgramKernel_output_value_kdet_of_shapes
import Theorems.Thm_GeneralCK_Certificates_CorrectionFactorizedProgramKernel_output_value_m11_of_shapes
import Theorems.Thm_GeneralCK_Correction_Mdet_pos_iff_Kfactored_pos
import Theorems.Thm_GeneralCK_Correction_Natural_kernel_eq_actual_ratio
import Theorems.Thm_GeneralCK_H_pos
import Theorems.Thm_GeneralCK_H_strictMonoOn

section
namespace GeneralCK.Certificates



namespace Jet2
open scoped Topology


















theorem soundAt_const (c t : ℝ) : (const c).SoundAt t :=
  ⟨hasDerivAt_const t c, hasDerivAt_const t 0⟩

































end Jet2
end GeneralCK.Certificates
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

theorem biasE_antitone : AntitoneOn biasE (Set.Icc 0 1) := by
  intro a ha b hb hab
  by_cases ha1 : a = 1
  · have he : b=a := by linarith [hb.2]
    rw [he]
  by_cases hb1 : b = 1
  · subst b
    have hnon := Real.binEntropy_nonneg (show 0 ≤ (1-a)/2 by linarith)
      (show (1-a)/2 ≤ 1 by linarith [ha.1])
    rw [biasE_eq_binEntropy (by linarith [ha.1]) (lt_of_le_of_ne ha.2 ha1)]
    norm_num [biasE]
    exact hnon
  rw [biasE_eq_binEntropy (by linarith [hb.1]) (lt_of_le_of_ne hb.2 hb1),
    biasE_eq_binEntropy (by linarith [ha.1]) (lt_of_le_of_ne ha.2 ha1)]
  exact Real.binEntropy_strictMonoOn.monotoneOn
    ⟨by linarith [hb.2],by linarith [hb.1]⟩
    ⟨by linarith [ha.2],by linarith [ha.1]⟩ (by linarith)



theorem contact_bracket {c y l u : ℝ} (hc : 0 ≤ c) (hc' : c ≤ 1)
    (hl : 0 ≤ l) (hu : u ≤ 1) (hlu : l ≤ u) (hy : 0 < y)
    (heq : biasE c = y*c) (hlo : y*l ≤ biasE l) (hhi : biasE u ≤ y*u) :
    Bounds l u c := by
  constructor
  · by_contra hn
    have hh : c < l := lt_of_not_ge hn
    have hm := biasE_antitone ⟨hc,hc'⟩ ⟨hl,hlu.trans hu⟩ hh.le
    have ht := mul_lt_mul_of_pos_left hh hy
    linarith
  · by_contra hn
    have hh : u < c := lt_of_not_ge hn
    have hm := biasE_antitone ⟨hl.trans hlu,hu⟩ ⟨hc,hc'⟩ hh.le
    have ht := mul_lt_mul_of_pos_left hh hy
    linarith

end GeneralCK.Certificates.Reflection
end

section
namespace GeneralCK.Certificates

namespace DyadicInterval



theorem contains_toReal_iff {p : ℕ} {a : DyadicInterval p} {x : ℝ} :
    a.toReal.Contains x ↔ a.Contains x := by
  change (a.lo:ℝ)/(scale p:ℝ) ≤ x ∧ x ≤ (a.hi:ℝ)/(scale p:ℝ) ↔ _
  rw [div_le_iff₀ (scale_cast_pos p),le_div_iff₀ (scale_cast_pos p)]
  simp only [Contains,mul_comm]

theorem toReal_positive_iff {p : ℕ} {a : DyadicInterval p} :
    0 < a.toReal.lo ↔ 0 < a.lo := by
  change 0 < (a.lo:ℝ)/(scale p:ℝ) ↔ _
  rw [div_pos_iff_of_pos_right (scale_cast_pos p)]
  exact Int.cast_pos

end DyadicInterval



namespace DyadicJetEnclosure
open DyadicInterval




































theorem subsetCheck_sound {p : ℕ} {b out : DyadicJetEnclosure p} {j : Jet2} {t : ℝ}
    (h : b.subsetCheck out=true) (hj : b.Contains j t) : out.Contains j t := by
  have hh := Bool.and_eq_true_iff.mp h
  have hvf := Bool.and_eq_true_iff.mp hh.1
  exact ⟨DyadicInterval.subsetCheck_sound hvf.1 hj.1,
    DyadicInterval.subsetCheck_sound hvf.2 hj.2.1,DyadicInterval.subsetCheck_sound hh.2 hj.2.2⟩







end DyadicJetEnclosure
end GeneralCK.Certificates
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



theorem biasB_pos {c : ℝ} (hc : 0 < c) (hc' : c < 1) : 0 < biasB c := by
  have hlog : Real.log (1-c*c) ≤ 0 := Real.log_nonpos (by nlinarith) (by nlinarith)
  unfold biasB
  linarith [log_two_pos]









end GeneralCK.Reflection
end

section
namespace GeneralCK.Certificates.ReflectionExpression
open Set
open GeneralCK.Certificates.Reflection
noncomputable section





@[simp] theorem sub_value (j k : Jet2) (t : ℝ) :
    (sub j k).value t = j.value t-k.value t := rfl
@[simp] theorem div_value (j k : Jet2) (t : ℝ) :
    (div j k).value t = j.value t/k.value t := by simp [div,Jet2.mul,Jet2.inv,div_eq_mul_inv]
@[simp] theorem pow_value (j : Jet2) (n : ℕ) (t : ℝ) :
    (pow j n).value t = (j.value t)^n := by
  induction n with
  | zero => simp [pow,Jet2.const]
  | succ n ih => simp [pow,Jet2.mul,ih,pow_succ,mul_comm]









@[simp] theorem entropy_value (j : Jet2) (t : ℝ) :
    (entropy j).value t = biasE (j.value t) := by
  simp [entropy,Jet2.const,Jet2.add,Jet2.mul,Jet2.log,biasE]
@[simp] theorem bfun_value (j : Jet2) (t : ℝ) :
    (bfun j).value t = biasB (j.value t) := by
  simp [bfun,Jet2.const,Jet2.log,biasB,pow_two]
@[simp] theorem atanh_value (j : Jet2) (t : ℝ) :
    (atanh j).value t = SmallMean.A (j.value t) := by
  simp [atanh,Jet2.const,Jet2.log,Jet2.add,SmallMean.A]









@[simp] theorem secant_value (c a e : Jet2) (t : ℝ) :
    (secant c a e).value t = biasS (c.value t) (a.value t) (e.value t) := by
  simp [secant,Jet2.mul,Jet2.add,Jet2.const,biasS,SmallMean.A,pow_two]













theorem normalized_value (a z : Jet2) (t : ℝ) :
    (normalized a z).value t = normalizedValue (a.value t) (z.value t) := by
  simp [normalized,normalizedValue,contactMinus,contactPlus,meanEntropy,radiusMinus,radiusPlus,
    Jet2.mul,Jet2.add,Jet2.const,Jet2.comp,reflectionContactJet]





end
end GeneralCK.Certificates.ReflectionExpression
end

section
namespace GeneralCK.Certificates
open Set

namespace Jet2



theorem soundOn_segment (c x : ℝ) (s : Set ℝ) : (segment c x).SoundOn s := by
  intro t _
  constructor
  · convert! ((hasDerivAt_id t).mul_const (x-c)).const_add c using 1
    simp [segment]
  · exact hasDerivAt_const t (x-c)

@[simp] theorem segment_value_zero (c x : ℝ) : (segment c x).value 0 = c := by
  simp [segment]

@[simp] theorem segment_value_one (c x : ℝ) : (segment c x).value 1 = x := by
  simp [segment]



end Jet2

namespace ReflectionExpression





@[simp] theorem segmentJet_value_zero (ac zc a z : ℝ) :
    (segmentJet ac zc a z).value 0 = normalizedValue ac zc := by
  simp [segmentJet,normalized_value]

@[simp] theorem segmentJet_value_one (ac zc a z : ℝ) :
    (segmentJet ac zc a z).value 1 = normalizedValue a z := by
  simp [segmentJet,normalized_value]









end ReflectionExpression
end GeneralCK.Certificates
end

section
namespace GeneralCK.Certificates



namespace BivariateJet2
























private theorem jet_ext {j k : Jet2} (hv : j.value=k.value)
    (hf : j.first=k.first) (hs : j.second=k.second) : j=k := by
  cases j; cases k; simp_all







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



















theorem soundOn_affineA (c x dz : ℝ) (s : Set ℝ) :
    (affineA c x).DirectionalSoundOn (x-c) dz s := by
  simpa only [DirectionalSoundOn,projection_affineA] using Jet2.soundOn_segment c x s

theorem soundOn_affineZ (c x da : ℝ) (s : Set ℝ) :
    (affineZ c x).DirectionalSoundOn da (x-c) s := by
  simpa only [DirectionalSoundOn,projection_affineZ] using Jet2.soundOn_segment c x s

end BivariateJet2
end GeneralCK.Certificates
end

section
namespace GeneralCK.Certificates.DyadicEntropy
open DyadicInterval





theorem half_contains (p : ℕ) : (half p).Contains ((2:ℝ)⁻¹) := by
  have htwo : (ofInt p 2).Contains (2:ℝ) := by simpa using ofInt_sound p 2
  exact recip_sound (by dsimp [ofInt]; have := scale_pos p; positivity) htwo















end GeneralCK.Certificates.DyadicEntropy
end

section
namespace GeneralCK.Certificates.ReflectionContactBounds
open JetBounds
open GeneralCK.Reflection
open GeneralCK.Certificates.Reflection

theorem first_eq {y : ℝ} (_hy : 0 < y) :
    reflectionContactJet.first y = -(biasContact y)^2/biasB (biasContact y) := by
  simp only [reflectionContactJet,biasRprime,neg_div,inv_neg,inv_div]

/-- Inverse-ratio second derivative expressed using positive denominators only. -/
theorem second_eq {y : ℝ} (hy : 0 < y) :
    reflectionContactJet.second y =
      2*(biasContact y)^3/(biasB (biasContact y))^2 -
      (biasContact y)^5/((1-(biasContact y)^2)*(biasB (biasContact y))^3) := by
  have hc := biasContact_mem hy
  have hb := (biasB_pos hc.1 hc.2).ne'
  have hg : 1-(biasContact y)^2 ≠ 0 := by nlinarith [hc.1,hc.2]
  simp only [reflectionContactJet,biasRsecond,biasRprime]
  field_simp [hc.1.ne',hb,hg]











end GeneralCK.Certificates.ReflectionContactBounds
end

section
namespace GeneralCK.Certificates.DyadicContact
open DyadicInterval
open GeneralCK.Reflection



theorem point_contains (p : ℕ) (z : ℤ) :
    (point z : DyadicInterval p).Contains ((z:ℝ)/(scale p:ℝ)) := by
  have hs := (scale_cast_pos p).ne'
  simp [point,DyadicInterval.Contains,mul_div_cancel₀,hs]

















theorem enclosure_sound {p : ℕ} {c B : DyadicInterval p} {y : ℝ} (hy : 0 < y)
    (hc : c.Contains (biasContact y)) (hB : B.Contains (Reflection.biasB (biasContact y)))
    (hBp : 0 < B.lo) (hgap : 0 < (gap c).lo) :
    (enclosure c B).Contains reflectionContactJet y := by
  have hr := recip_sound hBp hB
  have hc2 := mul_sound hc hc
  have hc3 := mul_sound hc2 hc
  have hr2 := mul_sound hr hr
  have hr3 := mul_sound hr2 hr
  have hone : (ofInt p 1).Contains (1:ℝ) := by simpa using ofInt_sound p 1
  have htwo : (ofInt p 2).Contains (2:ℝ) := by simpa using ofInt_sound p 2
  have hg := recip_sound hgap (sub_sound hone hc2)
  refine ⟨hc,?_,?_⟩
  · rw [ReflectionContactBounds.first_eq hy]
    simpa only [enclosure,div_eq_mul_inv,pow_two,neg_mul] using neg_sound (mul_sound hc2 hr)
  · rw [ReflectionContactBounds.second_eq hy]
    convert! sub_sound (mul_sound (mul_sound htwo hc3) hr2)
      (mul_sound (mul_sound (mul_sound hc3 hc2) hg) hr3) using 1
    simp only [div_eq_mul_inv,mul_inv_rev,pow_two]
    ring









end GeneralCK.Certificates.DyadicContact
end

section
namespace GeneralCK.Certificates
open DyadicInterval

namespace DyadicInterval.Contains







end DyadicInterval.Contains



namespace DyadicBivariateJetEnclosure
variable {p : ℕ}
















theorem contains_coordinateA {value : DyadicInterval p} {f : ℝ→ℝ} {t : ℝ}
    (h : value.Contains (f t)) : (coordinateA value).Contains (BivariateJet2.coordinateA f) t := by
  have h0 : (ofInt p 0).Contains (0:ℝ) := by simpa only [Int.cast_zero] using ofInt_sound p 0
  have h1 : (ofInt p 1).Contains (1:ℝ) := by simpa only [Int.cast_one] using ofInt_sound p 1
  exact ⟨h,h1,h0,h0,h0,h0⟩

theorem contains_coordinateZ {value : DyadicInterval p} {f : ℝ→ℝ} {t : ℝ}
    (h : value.Contains (f t)) : (coordinateZ value).Contains (BivariateJet2.coordinateZ f) t := by
  have h0 : (ofInt p 0).Contains (0:ℝ) := by simpa only [Int.cast_zero] using ofInt_sound p 0
  have h1 : (ofInt p 1).Contains (1:ℝ) := by simpa only [Int.cast_one] using ofInt_sound p 1
  exact ⟨h,h0,h1,h0,h0,h0⟩











theorem contains_const (p : ℕ) (c : ℤ) (t : ℝ) :
    (const p c).Contains (BivariateJet2.const c) t := by
  exact ⟨ofInt_sound p c,by simpa only [const,BivariateJet2.const,Int.cast_zero] using ofInt_sound p 0,by simpa only [const,BivariateJet2.const,Int.cast_zero] using ofInt_sound p 0,
    by simpa only [const,BivariateJet2.const,Int.cast_zero] using ofInt_sound p 0,by simpa only [const,BivariateJet2.const,Int.cast_zero] using ofInt_sound p 0,by simpa only [const,BivariateJet2.const,Int.cast_zero] using ofInt_sound p 0⟩







































end DyadicBivariateJetEnclosure
end GeneralCK.Certificates
end

section
namespace GeneralCK.Certificates.BivariateJetProgram










namespace Op













end Op





















theorem RegistersContain.nil (p : ℕ) (t : ℝ) :
    RegistersContain ([] : List (DyadicBivariateJetEnclosure p)) [] t := by
  refine ⟨rfl,fun i => ?_⟩
  simpa only [List.getD_nil,zeroBox,zeroJet,Int.cast_zero] using
    DyadicBivariateJetEnclosure.contains_const p 0 t

theorem RegistersSound.nil (da dz t : ℝ) : RegistersSound [] da dz t := by
  intro i
  simpa only [List.getD_nil,zeroJet,BivariateJet2.DirectionalSoundAt,
    BivariateJet2.projection_const] using Jet2.soundAt_const 0 t



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
open Set

namespace DyadicInterval

theorem contains_segment {p : ℕ} {box : DyadicInterval p} {c x t : ℝ}
    (hc : box.Contains c) (hx : box.Contains x) (ht : t ∈ Icc (0:ℝ) 1) :
    box.Contains ((Jet2.segment c x).value t) := by
  apply contains_toReal_iff.mp
  have hh := convex_Icc (𝕜 := ℝ) box.toReal.lo box.toReal.hi
    (contains_toReal_iff.mpr hc) (contains_toReal_iff.mpr hx)
    (sub_nonneg.mpr ht.2) ht.1 (show 1-t+t=1 by ring)
  simpa only [smul_eq_mul,Jet2.segment,JetBounds.Interval.Contains,Reflection.Bounds,Set.mem_Icc,
    show (1-t)*c+t*x=c+t*(x-c) by ring] using hh

end DyadicInterval

namespace DyadicJetEnclosure









end DyadicJetEnclosure

namespace JetProgram







end JetProgram
end GeneralCK.Certificates
end

section
namespace GeneralCK.Certificates.ProvedTranscendental
open DyadicInterval GeneralCK.Reflection GeneralCK.Certificates.Reflection



theorem log_of_endpoints {p : ℕ} {input out : DyadicInterval p}
    (hp : 0 < input.lo)
    (hl : out.Contains (Real.log ((input.lo:ℝ)/(scale p:ℝ))))
    (hu : out.Contains (Real.log ((input.hi:ℝ)/(scale p:ℝ)))) : LogEncloses input out := by
  intro x hx
  have hl' := contains_toReal_iff.mpr hl
  have hu' := contains_toReal_iff.mpr hu
  have hx' := contains_toReal_iff.mpr hx
  have hpos : 0 < input.toReal.lo := toReal_positive_iff.mpr hp
  apply contains_toReal_iff.mp
  exact ⟨hl'.1.trans (Real.log_le_log hpos hx'.1),
    (Real.log_le_log (hpos.trans_le hx'.1) hx'.2).trans hu'.2⟩







theorem entropy_encloses {p : ℕ} {c out two plus minus : DyadicInterval p}
    (h2 : two.Contains (Real.log 2))
    (hp : LogEncloses ((ofInt p 1).add c) plus)
    (hm : LogEncloses ((ofInt p 1).sub c) minus)
    (hsub : (entropyRaw c two plus minus).subsetCheck out=true)
    {x : ℝ} (hx : c.Contains x) : out.Contains (biasE x) := by
  have hone : (ofInt p 1).Contains (1:ℝ) := by simpa using ofInt_sound p 1
  have hplus := add_sound hone hx
  have hminus := sub_sound hone hx
  apply subsetCheck_sound hsub
  simpa only [entropyRaw,biasE,div_eq_mul_inv] using
    sub_sound h2 (mul_sound
      (add_sound (mul_sound hplus (hp _ hplus)) (mul_sound hminus (hm _ hminus)))
      (DyadicEntropy.half_contains p))



theorem denominator_encloses {p : ℕ} {c out two gapLog : DyadicInterval p}
    (h2 : two.Contains (Real.log 2))
    (hg : LogEncloses ((ofInt p 1).sub (c.mul c)) gapLog)
    (hsub : (denominatorRaw two gapLog).subsetCheck out=true)
    {x : ℝ} (hx : c.Contains x) : out.Contains (biasB x) := by
  have hone : (ofInt p 1).Contains (1:ℝ) := by simpa using ofInt_sound p 1
  have hgap := sub_sound hone (mul_sound hx hx)
  apply subsetCheck_sound hsub
  simpa only [denominatorRaw,biasB,div_eq_mul_inv] using
    sub_sound h2 (mul_sound (hg _ hgap) (DyadicEntropy.half_contains p))

/-- Only endpoint entropy proofs and exact arithmetic comparisons are required;
the actual contact follows from its already proved monotone inverse. -/
theorem contact_bracket {p : ℕ} {Y c elo ehi : DyadicInterval p}
    (hc0 : 0≤c.lo) (hc1 : c.hi≤scale p) (horder : c.lo≤c.hi) (hY : 0<Y.lo)
    (hel : elo.Contains (biasE ((c.lo:ℝ)/(scale p:ℝ))))
    (heu : ehi.Contains (biasE ((c.hi:ℝ)/(scale p:ℝ))))
    (hleft : (Y.mul (DyadicContact.point c.lo)).hi≤elo.lo)
    (hright : ehi.hi≤(Y.mul (DyadicContact.point c.hi)).lo)
    {y : ℝ} (hy : Y.Contains y) : c.Contains (biasContact y) := by
  have hyp : 0<y := positiveCheck_sound (by simpa [positiveCheck] using hY) hy
  have hs := scale_cast_pos p
  have hl : 0≤(c.lo:ℝ)/(scale p:ℝ) := div_nonneg (by exact_mod_cast hc0) hs.le
  have hu : (c.hi:ℝ)/(scale p:ℝ)≤1 := (div_le_one hs).mpr (by exact_mod_cast hc1)
  have hlu : (c.lo:ℝ)/(scale p:ℝ)≤(c.hi:ℝ)/(scale p:ℝ) :=
    (div_le_div_iff_of_pos_right hs).mpr (by exact_mod_cast horder)
  have hpl := mul_sound hy (DyadicContact.point_contains p c.lo)
  have hpu := mul_sound hy (DyadicContact.point_contains p c.hi)
  have hcmem := biasContact_mem hyp
  have heq : biasE (biasContact y)=y*biasContact y :=
    (div_eq_iff hcmem.1.ne').mp (biasR_biasContact hyp)
  apply contains_toReal_iff.mp
  apply Reflection.contact_bracket hcmem.1.le hcmem.2.le hl hu hlu hyp heq
  · have hcmp : ((Y.mul (DyadicContact.point c.lo)).hi:ℝ)≤(elo.lo:ℝ) := by exact_mod_cast hleft
    exact (mul_le_mul_iff_right₀ hs).mp (hpl.2.trans (hcmp.trans hel.1))
  · have hcmp : (ehi.hi:ℝ)≤((Y.mul (DyadicContact.point c.hi)).lo:ℝ) := by exact_mod_cast hright
    exact (mul_le_mul_iff_right₀ hs).mp (heu.2.trans (hcmp.trans hpu.1))

theorem contact_jet {p : ℕ} {Y c B : DyadicInterval p} {out : DyadicJetEnclosure p}
    (hY : 0<Y.lo)
    (hc : ∀ y : ℝ, Y.Contains y → c.Contains (biasContact y))
    (hB : ∀ x : ℝ, c.Contains x → B.Contains (biasB x))
    (hBp : 0<B.lo) (hgap : 0<(DyadicContact.gap c).lo)
    (hsub : (DyadicContact.enclosure c B).subsetCheck out=true)
    {y : ℝ} (hy : Y.Contains y) : out.Contains reflectionContactJet y := by
  have hyp : 0<y := positiveCheck_sound (by simpa [positiveCheck] using hY) hy
  have hcontact := hc y hy
  exact DyadicJetEnclosure.subsetCheck_sound hsub
    (DyadicContact.enclosure_sound hyp hcontact (hB _ hcontact) hBp hgap)

end GeneralCK.Certificates.ProvedTranscendental
end

section
namespace GeneralCK.Certificates.DyadicLogSeries
open scoped BigOperators















theorem state_sound {p : ℕ} {w : DyadicInterval p} {x : ℝ} (hw : w.Contains x) (n : ℕ) :
    (state w n).1.Contains (∑ k ∈ Finset.range n, x^(2*k+1)/(2*k+1)) ∧
      (state w n).2.Contains (x^(2*n+1)) := by
  induction n with
  | zero => simpa [state] using And.intro (DyadicInterval.ofInt_sound p 0) hw
  | succ n ih =>
    have hd : 0 < (DyadicInterval.ofInt p (2*(n:ℤ)+1)).lo := by
      change 0 < DyadicInterval.scale p*(2*(n:ℤ)+1)
      exact mul_pos (DyadicInterval.scale_pos p) (by omega)
    have hr := DyadicInterval.recip_sound hd (DyadicInterval.ofInt_sound p (2*(n:ℤ)+1))
    have ht := DyadicInterval.mul_sound ih.2 hr
    have hs := DyadicInterval.add_sound ih.1 ht
    have hp := DyadicInterval.mul_sound ih.2 (DyadicInterval.mul_sound hw hw)
    constructor
    · simpa only [state,Finset.sum_range_succ,Int.cast_add,Int.cast_mul,Int.cast_ofNat,
        Int.cast_one,Int.cast_natCast,div_eq_mul_inv] using hs
    · convert! hp using 1
      rw [show 2*(n+1)+1=(2*n+1)+2 by omega, pow_add, pow_two]

theorem denominator_sound {p : ℕ} {w : DyadicInterval p} {x : ℝ} (hw : w.Contains x) :
    (denominator w).Contains (1-x^2) := by
  simpa only [denominator,Int.cast_one,pow_two] using
    DyadicInterval.sub_sound (DyadicInterval.ofInt_sound p 1) (DyadicInterval.mul_sound hw hw)

theorem guard_sound {p : ℕ} {w : DyadicInterval p} {x : ℝ}
    (hg : guard w=true) (hw : w.Contains x) : 0 ≤ x ∧ x < 1 := by
  have hh := Bool.and_eq_true_iff.mp hg
  have hl : (0:ℝ) ≤ w.lo := by exact_mod_cast (of_decide_eq_true hh.1 : 0 ≤ w.lo)
  have hx : 0 ≤ x := nonneg_of_mul_nonneg_right (hl.trans hw.1) (DyadicInterval.scale_cast_pos p)
  have hd := DyadicInterval.positiveCheck_sound hh.2 (denominator_sound hw)
  exact ⟨hx, by nlinarith⟩

theorem partial_sound {p : ℕ} {w : DyadicInterval p} {x : ℝ} (hw : w.Contains x) (n : ℕ) :
    (partialSum w n).Contains (2*∑ k ∈ Finset.range n, x^(2*k+1)/(2*k+1)) := by
  simpa only [partialSum,Int.cast_ofNat] using
    DyadicInterval.mul_sound (DyadicInterval.ofInt_sound p 2) (state_sound hw n).1

theorem remainder_sound {p : ℕ} {w : DyadicInterval p} {x : ℝ}
    (hg : guard w=true) (hw : w.Contains x) (n : ℕ) :
    (remainder w n).Contains (2*x^(2*n+1)/(1-x^2)) := by
  have hd : 0 < (denominator w).lo := by
    simpa only [DyadicInterval.positiveCheck,decide_eq_true_eq] using (Bool.and_eq_true_iff.mp hg).2
  have hh := DyadicInterval.mul_sound
    (DyadicInterval.mul_sound (DyadicInterval.ofInt_sound p 2) (state_sound hw n).2)
    (DyadicInterval.recip_sound hd (denominator_sound hw))
  simpa only [remainder,Int.cast_ofNat,div_eq_mul_inv] using hh

/-- The analytic inequalities are proved in mathlib; this bridges them to the
integer-only partialSum-sum and outward remainder computation. -/
theorem enclosure_sound {p : ℕ} {w : DyadicInterval p} {x : ℝ}
    (hg : guard w=true) (hw : w.Contains x) (n : ℕ) :
    (enclosure w n).Contains (Real.log ((1+x)/(1-x))) := by
  have hx := guard_sound hg hw
  have hl := Real.sum_range_le_log_div hx.1 hx.2 n
  have hu := Real.log_div_le_sum_range_add hx.1 hx.2 n
  have hs := partial_sound hw n
  have ht := DyadicInterval.add_sound hs (remainder_sound hg hw n)
  have hrealL : 2*∑ k ∈ Finset.range n, x^(2*k+1)/(2*k+1) ≤ Real.log ((1+x)/(1-x)) := by linarith
  have hrealH : Real.log ((1+x)/(1-x)) ≤
      2*∑ k ∈ Finset.range n, x^(2*k+1)/(2*k+1)+2*x^(2*n+1)/(1-x^2) := by
    rw [mul_div_assoc]
    linarith
  exact ⟨hs.1.trans (mul_le_mul_of_nonneg_left hrealL (DyadicInterval.scale_cast_pos p).le),
    (mul_le_mul_of_nonneg_left hrealH (DyadicInterval.scale_cast_pos p).le).trans ht.2⟩













end GeneralCK.Certificates.DyadicLogSeries
end

section
namespace GeneralCK.Certificates.DyadicFastLog



theorem fraction_sound (p : ℕ) (a : ℤ) {b : ℤ} (hb : 0 < b) :
    (fraction p a b).Contains ((a:ℝ)/b) := by
  have hb' : (0:ℝ) < b := by exact_mod_cast hb
  have hl : (DyadicInterval.floorDiv (DyadicInterval.scale p*a) b:ℝ)*b ≤
      (DyadicInterval.scale p:ℝ)*a := by
    exact_mod_cast DyadicInterval.floorDiv_mul_le (DyadicInterval.scale p*a) hb
  have hu : (DyadicInterval.scale p:ℝ)*a ≤
      (DyadicInterval.ceilDiv (DyadicInterval.scale p*a) b:ℝ)*b := by
    exact_mod_cast DyadicInterval.le_ceilDiv_mul (DyadicInterval.scale p*a) hb
  change _ ≤ _ ∧ _ ≤ _
  rw [← mul_div_assoc]
  exact ⟨(le_div_iff₀ hb').mpr hl,(div_le_iff₀ hb').mpr hu⟩







theorem check_sound {p : ℕ} {a b : ℤ} {e n : ℕ} {out : DyadicInterval p}
    (hc : check a b e n out=true) : out.Contains (Real.log ((a:ℝ)/b)) := by
  have h3 := Bool.and_eq_true_iff.mp hc
  have h2 := Bool.and_eq_true_iff.mp h3.1
  have h1 := Bool.and_eq_true_iff.mp h2.1
  have hab : 0<a ∧ 0<b := of_decide_eq_true h1.1
  have ha : (0:ℝ)<a := by exact_mod_cast hab.1
  have hb : (0:ℝ)<b := by exact_mod_cast hab.2
  have ht := DyadicLogSeries.enclosure_sound h1.2 (fraction_sound p 1 (by norm_num : (0:ℤ)<3)) n
  norm_num at ht
  have hd : 0 < b+a*2^e := add_pos hab.2 (mul_pos hab.1 (by positivity))
  have hr := DyadicLogSeries.enclosure_sound h2.2 (fraction_sound p (b-a*2^e) hd) n
  have heq : (1+((b-a*2^e:ℤ):ℝ)/(b+a*2^e:ℤ))/
      (1-((b-a*2^e:ℤ):ℝ)/(b+a*2^e:ℤ)) = (b:ℝ)/(a*2^e) := by
    push_cast
    have hp : (0:ℝ)<2^e := by positivity
    field_simp
    ring
  rw [heq] at hr
  have hs := DyadicInterval.neg_sound (DyadicInterval.add_sound
    (DyadicInterval.mul_sound (DyadicInterval.ofInt_sound p e) ht) hr)
  have hl : -((e:ℝ)*Real.log 2+Real.log ((b:ℝ)/(a*2^e))) = Real.log ((a:ℝ)/b) := by
    rw [Real.log_div hb.ne' (mul_pos ha (by positivity)).ne',
      Real.log_mul ha.ne' (by positivity),Real.log_pow,Real.log_div ha.ne' hb.ne']
    ring
  simp only [Int.cast_natCast] at hs
  rw [hl] at hs
  exact DyadicInterval.subsetCheck_sound h3.2 hs

end GeneralCK.Certificates.DyadicFastLog
end

section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LaneCBRB2Cell000062Endpoints
open GeneralCK.Certificates
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

noncomputable def lift40 (a : DyadicInterval 40) : DyadicInterval 64 :=
  ⟨a.lo*16777216, a.hi*16777216⟩

theorem lift40_contains {a : DyadicInterval 40} {x : ℝ} :
    (lift40 a).Contains x ↔ a.Contains x := by
  simp only [DyadicInterval.Contains, lift40, Int.cast_mul, Int.cast_ofNat]
  norm_num [DyadicInterval.scale]
  constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]

theorem direct {z : ℤ} {e n : ℕ} {a : DyadicInterval 40}
    (hc : DyadicFastLog.check z 1099511627776 e n (lift40 a)=true) :
    a.Contains (Real.log ((z:ℝ)/1099511627776)) := by
  apply lift40_contains.mp
  simpa only [Int.cast_ofNat] using DyadicFastLog.check_sound hc

theorem reciprocal {z : ℤ} {e n : ℕ} {a : DyadicInterval 40}
    (hc : DyadicFastLog.check 1099511627776 z e n (lift40 a.neg)=true) :
    a.Contains (Real.log ((z:ℝ)/1099511627776)) := by
  have h := lift40_contains.mp (DyadicFastLog.check_sound hc)
  have hn := DyadicInterval.neg_sound h
  rw [← Real.log_inv, inv_div] at hn
  simpa only [DyadicInterval.neg, neg_neg, Int.cast_ofNat] using hn

noncomputable def sharedTwo : DyadicInterval 64 := ⟨12786308645202655420,12786308645202662926⟩
theorem sharedTwo_eq : DyadicLogSeries.enclosure (DyadicFastLog.fraction 64 1 3) 16=sharedTwo := by rfl
noncomputable def out_w0 : DyadicInterval 40 := ⟨-2499969724352,-2499969666496⟩
theorem checked_w0 : DyadicFastLog.check 113172388249 1099511627776 3 16 (lift40 out_w0)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w0 : out_w0.Contains (Real.log ((113172388249:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w0

noncomputable def out_w1 : DyadicInterval 40 := ⟨-2499969724352,-2499969666496⟩
theorem checked_w1 : DyadicFastLog.check 113172388250 1099511627776 3 16 (lift40 out_w1)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w1 : out_w1.Contains (Real.log ((113172388250:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w1

noncomputable def out_w2 : DyadicInterval 40 := ⟨-119430089600,-119430089536⟩
theorem checked_w2 : DyadicFastLog.check 986339239526 1099511627776 0 16 (lift40 out_w2)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w2 : out_w2.Contains (Real.log ((986339239526:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w2

noncomputable def out_w3 : DyadicInterval 40 := ⟨-119430089600,-119430089536⟩
theorem checked_w3 : DyadicFastLog.check 986339239527 1099511627776 0 16 (lift40 out_w3)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w3 : out_w3.Contains (Real.log ((986339239527:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w3

noncomputable def out_w4 : DyadicInterval 40 := ⟨-2073439125696,-2073439086976⟩
theorem checked_w4 : DyadicFastLog.check 166807344250 1099511627776 2 16 (lift40 out_w4)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w4 : out_w4.Contains (Real.log ((166807344250:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w4

noncomputable def out_w5 : DyadicInterval 40 := ⟨-2073439125632,-2073439086976⟩
theorem checked_w5 : DyadicFastLog.check 166807344252 1099511627776 2 16 (lift40 out_w5)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w5 : out_w5.Contains (Real.log ((166807344252:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w5

noncomputable def out_w6 : DyadicInterval 40 := ⟨-180906152448,-180906152384⟩
theorem checked_w6 : DyadicFastLog.check 932704283524 1099511627776 0 16 (lift40 out_w6)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w6 : out_w6.Contains (Real.log ((932704283524:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w6

noncomputable def out_w7 : DyadicInterval 40 := ⟨-180906152448,-180906152384⟩
theorem checked_w7 : DyadicFastLog.check 932704283526 1099511627776 0 16 (lift40 out_w7)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w7 : out_w7.Contains (Real.log ((932704283526:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w7

noncomputable def out_w8 : DyadicInterval 40 := ⟨762123383616,762123402880⟩
theorem checked_w8 : DyadicFastLog.check 1099511627776 2199023255552 1 16 (lift40 out_w8.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w8 : out_w8.Contains (Real.log ((2199023255552:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w8

noncomputable def out_w9 : DyadicInterval 40 := ⟨93549374272,93549374336⟩
theorem checked_w9 : DyadicFastLog.check 1099511627776 1197156027392 0 16 (lift40 out_w9.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w9 : out_w9.Contains (Real.log ((1197156027392:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w9

noncomputable def out_w10 : DyadicInterval 40 := ⟨-102255262464,-102255262400⟩
theorem checked_w10 : DyadicFastLog.check 1001867228160 1099511627776 0 16 (lift40 out_w10)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w10 : out_w10.Contains (Real.log ((1001867228160:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w10

noncomputable def out_w11 : DyadicInterval 40 := ⟨93549496768,93549496832⟩
theorem checked_w11 : DyadicFastLog.check 1099511627776 1197156160768 0 16 (lift40 out_w11.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w11 : out_w11.Contains (Real.log ((1197156160768:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w11

noncomputable def out_w12 : DyadicInterval 40 := ⟨-102255408832,-102255408768⟩
theorem checked_w12 : DyadicFastLog.check 1001867094784 1099511627776 0 16 (lift40 out_w12)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w12 : out_w12.Contains (Real.log ((1001867094784:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w12

noncomputable def out_w13 : DyadicInterval 40 := ⟨-8705912000,-8705911936⟩
theorem checked_w13 : DyadicFastLog.check 1090840091629 1099511627776 0 16 (lift40 out_w13)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w13 : out_w13.Contains (Real.log ((1090840091629:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w13

noncomputable def out_w14 : DyadicInterval 40 := ⟨-8705888128,-8705888064⟩
theorem checked_w14 : DyadicFastLog.check 1090840115320 1099511627776 0 16 (lift40 out_w14)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w14 : out_w14.Contains (Real.log ((1090840115320:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w14

noncomputable def out_w15 : DyadicInterval 40 := ⟨195804636736,195804636800⟩
theorem checked_w15 : DyadicFastLog.check 1099511627776 1313833745012 0 16 (lift40 out_w15.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w15 : out_w15.Contains (Real.log ((1313833745012:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w15

noncomputable def out_w16 : DyadicInterval 40 := ⟨195804905600,195804905664⟩
theorem checked_w16 : DyadicFastLog.check 1099511627776 1313834066296 0 16 (lift40 out_w16.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w16 : out_w16.Contains (Real.log ((1313834066296:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w16

noncomputable def out_w17 : DyadicInterval 40 := ⟨2380539576896,2380539634752⟩
theorem checked_w17 : DyadicFastLog.check 1099511627776 9582650676195 3 16 (lift40 out_w17.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w17 : out_w17.Contains (Real.log ((9582650676195:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w17

noncomputable def out_w18 : DyadicInterval 40 := ⟨2380539576896,2380539634752⟩
theorem checked_w18 : DyadicFastLog.check 1099511627776 9582650676291 3 16 (lift40 out_w18.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w18 : out_w18.Contains (Real.log ((9582650676291:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w18

noncomputable def out_w19 : DyadicInterval 40 := ⟨1892532934592,1892532973184⟩
theorem checked_w19 : DyadicFastLog.check 1099511627776 6147925977778 2 16 (lift40 out_w19.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w19 : out_w19.Contains (Real.log ((6147925977778:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w19

noncomputable def out_w20 : DyadicInterval 40 := ⟨1892532934592,1892532973184⟩
theorem checked_w20 : DyadicFastLog.check 1099511627776 6147925977866 2 16 (lift40 out_w20.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w20 : out_w20.Contains (Real.log ((6147925977866:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w20

noncomputable def out_w21 : DyadicInterval 40 := ⟨-2502058066176,-2502058008320⟩
theorem checked_w21 : DyadicFastLog.check 112957639884 1099511627776 3 16 (lift40 out_w21)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w21 : out_w21.Contains (Real.log ((112957639884:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w21

noncomputable def out_w22 : DyadicInterval 40 := ⟨-2497885341504,-2497885283648⟩
theorem checked_w22 : DyadicFastLog.check 113387136615 1099511627776 3 16 (lift40 out_w22)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w22 : out_w22.Contains (Real.log ((113387136615:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w22

noncomputable def out_w23 : DyadicInterval 40 := ⟨-119669504256,-119669504192⟩
theorem checked_w23 : DyadicFastLog.check 986124491161 1099511627776 0 16 (lift40 out_w23)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w23 : out_w23.Contains (Real.log ((986124491161:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w23

noncomputable def out_w24 : DyadicInterval 40 := ⟨-119190727104,-119190727040⟩
theorem checked_w24 : DyadicFastLog.check 986553987892 1099511627776 0 16 (lift40 out_w24)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w24 : out_w24.Contains (Real.log ((986553987892:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w24

noncomputable def out_w25 : DyadicInterval 40 := ⟨-2080104746176,-2080104707456⟩
theorem checked_w25 : DyadicFastLog.check 165799159397 1099511627776 2 16 (lift40 out_w25)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w25 : out_w25.Contains (Real.log ((165799159397:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w25

noncomputable def out_w26 : DyadicInterval 40 := ⟨-2066808724544,-2066808685888⟩
theorem checked_w26 : DyadicFastLog.check 167816284080 1099511627776 2 16 (lift40 out_w26)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w26 : out_w26.Contains (Real.log ((167816284080:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w26

noncomputable def out_w27 : DyadicInterval 40 := ⟨-182096177536,-182096177472⟩
theorem checked_w27 : DyadicFastLog.check 931695343696 1099511627776 0 16 (lift40 out_w27)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w27 : out_w27.Contains (Real.log ((931695343696:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w27

noncomputable def out_w28 : DyadicInterval 40 := ⟨-179718302976,-179718302912⟩
theorem checked_w28 : DyadicFastLog.check 933712468379 1099511627776 0 16 (lift40 out_w28)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w28 : out_w28.Contains (Real.log ((933712468379:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w28

noncomputable def out_w29 : DyadicInterval 40 := ⟨91002385216,91002385280⟩
theorem checked_w29 : DyadicFastLog.check 1099511627776 1194386057216 0 16 (lift40 out_w29.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w29 : out_w29.Contains (Real.log ((1194386057216:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w29

noncomputable def out_w30 : DyadicInterval 40 := ⟨-99219518976,-99219518912⟩
theorem checked_w30 : DyadicFastLog.check 1004637198336 1099511627776 0 16 (lift40 out_w30)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w30 : out_w30.Contains (Real.log ((1004637198336:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w30

noncomputable def out_w31 : DyadicInterval 40 := ⟨96117580864,96117580928⟩
theorem checked_w31 : DyadicFastLog.check 1099511627776 1199955577088 0 16 (lift40 out_w31.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w31 : out_w31.Contains (Real.log ((1199955577088:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w31

noncomputable def out_w32 : DyadicInterval 40 := ⟨-105331963712,-105331963648⟩
theorem checked_w32 : DyadicFastLog.check 999067678464 1099511627776 0 16 (lift40 out_w32)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w32 : out_w32.Contains (Real.log ((999067678464:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w32

noncomputable def out_w33 : DyadicInterval 40 := ⟨-9214382848,-9214382784⟩
theorem checked_w33 : DyadicFastLog.check 1090335747595 1099511627776 0 16 (lift40 out_w33)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w33 : out_w33.Contains (Real.log ((1090335747595:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w33

noncomputable def out_w34 : DyadicInterval 40 := ⟨-8217133760,-8217133696⟩
theorem checked_w34 : DyadicFastLog.check 1091325122846 1099511627776 0 16 (lift40 out_w34)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w34 : out_w34.Contains (Real.log ((1091325122846:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w34

noncomputable def out_w35 : DyadicInterval 40 := ⟨190221904192,190221904256⟩
theorem checked_w35 : DyadicFastLog.check 1099511627776 1307179706402 0 16 (lift40 out_w35.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w35 : out_w35.Contains (Real.log ((1307179706402:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w35

noncomputable def out_w36 : DyadicInterval 40 := ⟨201449544512,201449544576⟩
theorem checked_w36 : DyadicFastLog.check 1099511627776 1320596330222 0 16 (lift40 out_w36.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w36 : out_w36.Contains (Real.log ((1320596330222:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w36

noncomputable def out_w37 : DyadicInterval 40 := ⟨2378215779456,2378215837312⟩
theorem checked_w37 : DyadicFastLog.check 1099511627776 9562419308177 3 16 (lift40 out_w37.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w37 : out_w37.Contains (Real.log ((9562419308177:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w37

noncomputable def out_w38 : DyadicInterval 40 := ⟨2382867281216,2382867339072⟩
theorem checked_w38 : DyadicFastLog.check 1099511627776 9602958969664 3 16 (lift40 out_w38.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w38 : out_w38.Contains (Real.log ((9602958969664:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w38

noncomputable def out_w39 : DyadicInterval 40 := ⟨1884712508416,1884712547008⟩
theorem checked_w39 : DyadicFastLog.check 1099511627776 6104353159495 2 16 (lift40 out_w39.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w39 : out_w39.Contains (Real.log ((6104353159495:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w39

noncomputable def out_w40 : DyadicInterval 40 := ⟨1900386404544,1900386443136⟩
theorem checked_w40 : DyadicFastLog.check 1099511627776 6191995904660 2 16 (lift40 out_w40.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w40 : out_w40.Contains (Real.log ((6191995904660:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w40

end LaneCBRB2Cell000062Endpoints

namespace GeneralCK.Certificates.LaneCB.RB2Cell000062
open Set LaneCBRB2Cell000062Endpoints
open BivariateJetProgram (RegistersContain RegistersSound zeroBox zeroJet)
open BivariateProvedProgram
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
theorem lc0 : ProvedTranscendental.LogEncloses (⟨113172388249,113172388250⟩ : DyadicInterval 40) (⟨-2499969724352,-2499969666496⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w1
theorem lc1 : ProvedTranscendental.LogEncloses (⟨986339239526,986339239527⟩ : DyadicInterval 40) (⟨-119430089600,-119430089536⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w2
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w3
theorem lc2 : ProvedTranscendental.LogEncloses (⟨166807344250,166807344252⟩ : DyadicInterval 40) (⟨-2073439125696,-2073439086976⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w4
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w5
theorem lc3 : ProvedTranscendental.LogEncloses (⟨932704283524,932704283526⟩ : DyadicInterval 40) (⟨-180906152448,-180906152384⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w6
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w7
theorem lc4 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
theorem lc5 : ProvedTranscendental.LogEncloses (⟨1197156027392,1197156027392⟩ : DyadicInterval 40) (⟨93549374272,93549374336⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w9
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w9
theorem lc6 : ProvedTranscendental.LogEncloses (⟨1001867228160,1001867228160⟩ : DyadicInterval 40) (⟨-102255262464,-102255262400⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w10
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w10
theorem lc7 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
theorem lc8 : ProvedTranscendental.LogEncloses (⟨1197156160768,1197156160768⟩ : DyadicInterval 40) (⟨93549496768,93549496832⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w11
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w11
theorem lc9 : ProvedTranscendental.LogEncloses (⟨1001867094784,1001867094784⟩ : DyadicInterval 40) (⟨-102255408832,-102255408768⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w12
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w12
theorem lc10 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
theorem lc11 : ProvedTranscendental.LogEncloses (⟨1090840091629,1090840115320⟩ : DyadicInterval 40) (⟨-8705912000,-8705888064⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w13
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w14
theorem lc12 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
theorem lc13 : ProvedTranscendental.LogEncloses (⟨1197156027392,1197156160768⟩ : DyadicInterval 40) (⟨93549374272,93549496832⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w9
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w11
theorem lc14 : ProvedTranscendental.LogEncloses (⟨1001867094784,1001867228160⟩ : DyadicInterval 40) (⟨-102255408832,-102255262400⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w12
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w10
theorem lc15 : ProvedTranscendental.LogEncloses (⟨1090840091629,1090840115320⟩ : DyadicInterval 40) (⟨-8705912000,-8705888064⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w13
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w14
theorem lc16 : ProvedTranscendental.LogEncloses (⟨1313833745012,1313834066296⟩ : DyadicInterval 40) (⟨195804636736,195804905664⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w15
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w16
theorem lc17 : ProvedTranscendental.LogEncloses (⟨9582650676195,9582650676291⟩ : DyadicInterval 40) (⟨2380539576896,2380539634752⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w17
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w18
theorem lc18 : ProvedTranscendental.LogEncloses (⟨6147925977778,6147925977866⟩ : DyadicInterval 40) (⟨1892532934592,1892532973184⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w19
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w20
theorem lc19 : ProvedTranscendental.LogEncloses (⟨112957639884,113387136615⟩ : DyadicInterval 40) (⟨-2502058066176,-2497885283648⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w21
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w22
theorem lc20 : ProvedTranscendental.LogEncloses (⟨986124491161,986553987892⟩ : DyadicInterval 40) (⟨-119669504256,-119190727040⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w23
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w24
theorem lc21 : ProvedTranscendental.LogEncloses (⟨165799159397,167816284080⟩ : DyadicInterval 40) (⟨-2080104746176,-2066808685888⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w25
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w26
theorem lc22 : ProvedTranscendental.LogEncloses (⟨931695343696,933712468379⟩ : DyadicInterval 40) (⟨-182096177536,-179718302912⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w27
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w28
theorem lc23 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
theorem lc24 : ProvedTranscendental.LogEncloses (⟨1194386057216,1194386057216⟩ : DyadicInterval 40) (⟨91002385216,91002385280⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w29
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w29
theorem lc25 : ProvedTranscendental.LogEncloses (⟨1004637198336,1004637198336⟩ : DyadicInterval 40) (⟨-99219518976,-99219518912⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w30
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w30
theorem lc26 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
theorem lc27 : ProvedTranscendental.LogEncloses (⟨1199955577088,1199955577088⟩ : DyadicInterval 40) (⟨96117580864,96117580928⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w31
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w31
theorem lc28 : ProvedTranscendental.LogEncloses (⟨999067678464,999067678464⟩ : DyadicInterval 40) (⟨-105331963712,-105331963648⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w32
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w32
theorem lc29 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
theorem lc30 : ProvedTranscendental.LogEncloses (⟨1090335747595,1091325122846⟩ : DyadicInterval 40) (⟨-9214382848,-8217133696⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w33
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w34
theorem lc31 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
theorem lc32 : ProvedTranscendental.LogEncloses (⟨1194386057216,1199955577088⟩ : DyadicInterval 40) (⟨91002385216,96117580928⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w29
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w31
theorem lc33 : ProvedTranscendental.LogEncloses (⟨999067678464,1004637198336⟩ : DyadicInterval 40) (⟨-105331963712,-99219518912⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w32
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w30
theorem lc34 : ProvedTranscendental.LogEncloses (⟨1090335747595,1091325122846⟩ : DyadicInterval 40) (⟨-9214382848,-8217133696⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w33
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w34
theorem lc35 : ProvedTranscendental.LogEncloses (⟨1307179706402,1320596330222⟩ : DyadicInterval 40) (⟨190221904192,201449544576⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w35
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w36
theorem lc36 : ProvedTranscendental.LogEncloses (⟨9562419308177,9602958969664⟩ : DyadicInterval 40) (⟨2378215779456,2382867339072⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w37
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w38
theorem lc37 : ProvedTranscendental.LogEncloses (⟨6104353159495,6191995904660⟩ : DyadicInterval 40) (⟨1884712508416,1900386443136⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w39
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w40
theorem ew11_ok (x : ℝ) (hx : (⟨97644399616,97644399616⟩ : DyadicInterval 40).Contains x) : (⟨757781910184,757781929513⟩ : DyadicInterval 40).Contains (Reflection.biasE x) := by
  exact ProvedTranscendental.entropy_encloses (c:=(⟨97644399616,97644399616⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (plus:=(⟨93549374272,93549374336⟩ : DyadicInterval 40)) (minus:=(⟨-102255262464,-102255262400⟩ : DyadicInterval 40))
    (lc4 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc5 lc6 (by decide) hx
theorem ew14_ok (x : ℝ) (hx : (⟨97644532992,97644532992⟩ : DyadicInterval 40).Contains x) : (⟨757781898305,757781917635⟩ : DyadicInterval 40).Contains (Reflection.biasE x) := by
  exact ProvedTranscendental.entropy_encloses (c:=(⟨97644532992,97644532992⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (plus:=(⟨93549496768,93549496832⟩ : DyadicInterval 40)) (minus:=(⟨-102255408832,-102255408768⟩ : DyadicInterval 40))
    (lc7 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc8 lc9 (by decide) hx
theorem ew35_ok (x : ℝ) (hx : (⟨94874429440,94874429440⟩ : DyadicInterval 40).Contains x) : (⟨758025036483,758025055813⟩ : DyadicInterval 40).Contains (Reflection.biasE x) := by
  exact ProvedTranscendental.entropy_encloses (c:=(⟨94874429440,94874429440⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (plus:=(⟨91002385216,91002385280⟩ : DyadicInterval 40)) (minus:=(⟨-99219518976,-99219518912⟩ : DyadicInterval 40))
    (lc23 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc24 lc25 (by decide) hx
theorem ew38_ok (x : ℝ) (hx : (⟨100443949312,100443949312⟩ : DyadicInterval 40).Contains x) : (⟨757529040706,757529060036⟩ : DyadicInterval 40).Contains (Reflection.biasE x) := by
  exact ProvedTranscendental.entropy_encloses (c:=(⟨100443949312,100443949312⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (plus:=(⟨96117580864,96117580928⟩ : DyadicInterval 40)) (minus:=(⟨-105331963712,-105331963648⟩ : DyadicInterval 40))
    (lc26 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc27 lc28 (by decide) hx
theorem bw17_ok (x : ℝ) (hx : (⟨97644399616,97644532992⟩ : DyadicInterval 40).Contains x) : (⟨766476327648,766476358880⟩ : DyadicInterval 40).Contains (Reflection.biasB x) := by
  exact ProvedTranscendental.denominator_encloses (c:=(⟨97644399616,97644532992⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (gapLog:=(⟨-8705912000,-8705888064⟩ : DyadicInterval 40))
    (lc10 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc11 (by decide) hx
theorem bw41_ok (x : ℝ) (hx : (⟨94874429440,100443949312⟩ : DyadicInterval 40).Contains x) : (⟨766231950464,766730594304⟩ : DyadicInterval 40).Contains (Reflection.biasB x) := by
  exact ProvedTranscendental.denominator_encloses (c:=(⟨94874429440,100443949312⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (gapLog:=(⟨-9214382848,-8217133696⟩ : DyadicInterval 40))
    (lc29 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc30 (by decide) hx
theorem brcenter28_contact (y : ℝ) (hy : (⟨8532895339278,8532895462265⟩ : DyadicInterval 40).Contains y) : (⟨97644399616,97644532992⟩ : DyadicInterval 40).Contains (Reflection.biasContact y) := by
  exact ProvedTranscendental.contact_bracket (Y:=(⟨8532895339278,8532895462265⟩ : DyadicInterval 40)) (c:=(⟨97644399616,97644532992⟩ : DyadicInterval 40)) (elo:=(⟨757781910184,757781929513⟩ : DyadicInterval 40)) (ehi:=(⟨757781898305,757781917635⟩ : DyadicInterval 40))
    (by decide) (by decide) (by decide) (by decide)
    (ew11_ok _ (DyadicContact.point_contains 40 97644399616)) (ew14_ok _ (DyadicContact.point_contains 40 97644532992))
    (by decide) (by decide) hy
theorem brcenter28_jet (y : ℝ) (hy : (⟨8532895339278,8532895462265⟩ : DyadicInterval 40).Contains y) : (⟨⟨97644399616,97644532992⟩,⟨-12439333716,-12439299223⟩,⟨3151310250,3151323635⟩⟩ : DyadicJetEnclosure 40).Contains reflectionContactJet y := by
  exact ProvedTranscendental.contact_jet (c:=(⟨97644399616,97644532992⟩ : DyadicInterval 40)) (B:=(⟨766476327648,766476358880⟩ : DyadicInterval 40)) (by decide) brcenter28_contact bw17_ok (by decide) (by decide) (by decide) hy
theorem brwhole28_contact (y : ℝ) (hy : (⟨8292311845117,8784840747918⟩ : DyadicInterval 40).Contains y) : (⟨94874429440,100443949312⟩ : DyadicInterval 40).Contains (Reflection.biasContact y) := by
  exact ProvedTranscendental.contact_bracket (Y:=(⟨8292311845117,8784840747918⟩ : DyadicInterval 40)) (c:=(⟨94874429440,100443949312⟩ : DyadicInterval 40)) (elo:=(⟨758025036483,758025055813⟩ : DyadicInterval 40)) (ehi:=(⟨757529040706,757529060036⟩ : DyadicInterval 40))
    (by decide) (by decide) (by decide) (by decide)
    (ew35_ok _ (DyadicContact.point_contains 40 94874429440)) (ew38_ok _ (DyadicContact.point_contains 40 100443949312))
    (by decide) (by decide) hy
theorem brwhole28_jet (y : ℝ) (hy : (⟨8292311845117,8784840747918⟩ : DyadicInterval 40).Contains y) : (⟨⟨94874429440,100443949312⟩,⟨-13167014177,-11739661138⟩,⟨2884462549,3436453209⟩⟩ : DyadicJetEnclosure 40).Contains reflectionContactJet y := by
  exact ProvedTranscendental.contact_jet (c:=(⟨94874429440,100443949312⟩ : DyadicInterval 40)) (B:=(⟨766231950464,766730594304⟩ : DyadicInterval 40)) (by decide) brwhole28_contact bw41_ok (by decide) (by decide) (by decide) hy
noncomputable def centerInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨113172388249,113172388250⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨135076721459,135076721460⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def centerBoxes0 := centerInitial
noncomputable def centerStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes1 := centerStep0.proposed :: centerBoxes0
theorem centerAccepted0 : StepValid centerStep0.shape centerBoxes0 centerStep0.proposed := by
  dsimp only [StepValid,centerStep0]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes2 := centerStep1.proposed :: centerBoxes1
theorem centerAccepted1 : StepValid centerStep1.shape centerBoxes1 centerStep1.proposed := by
  dsimp only [StepValid,centerStep1]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-113172388250,-113172388249⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes3 := centerStep2.proposed :: centerBoxes2
theorem centerAccepted2 : StepValid centerStep2.shape centerBoxes2 centerStep2.proposed := by
  dsimp only [StepValid,centerStep2]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨436583425638,436583425639⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes4 := centerStep3.proposed :: centerBoxes3
theorem centerAccepted3 : StepValid centerStep3.shape centerBoxes3 centerStep3.proposed := by
  dsimp only [StepValid,centerStep3]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨53634956001,53634956002⟩,⟨-135076721460,-135076721459⟩,⟨436583425638,436583425639⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes5 := centerStep4.proposed :: centerBoxes4
theorem centerAccepted4 : StepValid centerStep4.shape centerBoxes4 centerStep4.proposed := by
  dsimp only [StepValid,centerStep4]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨166807344250,166807344252⟩,⟨964434906316,964434906317⟩,⟨436583425638,436583425639⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes6 := centerStep5.proposed :: centerBoxes5
theorem centerAccepted5 : StepValid centerStep5.shape centerBoxes5 centerStep5.proposed := by
  dsimp only [StepValid,centerStep5]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨53634956000,53634956003⟩,⟨-135076721460,-135076721459⟩,⟨436583425638,436583425639⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes7 := centerStep6.proposed :: centerBoxes6
theorem centerAccepted6 : StepValid centerStep6.shape centerBoxes6 centerStep6.proposed := by
  dsimp only [StepValid,centerStep6]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep7 : Instruction 40 := ⟨.log 7,⟨⟨-2499969724352,-2499969666496⟩,⟨10682162303971,10682162304067⟩,⟨0,0⟩,⟨-103781159387318,-103781159385452⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes8 := centerStep7.proposed :: centerBoxes7
theorem centerAccepted7 : StepValid centerStep7.shape centerBoxes7 centerStep7.proposed := by
  dsimp only [StepValid,centerStep7]
  exact ⟨by decide,by decide,lc0,by decide⟩
noncomputable def centerStep8 : Instruction 40 := ⟨.mul 8 0,⟨⟨-257321102488,-257321096530⟩,⟨-1400458096586,-1400458038710⟩,⟨0,0⟩,⟨10682162303779,10682162304259⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes9 := centerStep8.proposed :: centerBoxes8
theorem centerAccepted8 : StepValid centerStep8.shape centerBoxes8 centerStep8.proposed := by
  dsimp only [StepValid,centerStep8]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep9 : Instruction 40 := ⟨.neg 0,⟨⟨257321096530,257321102488⟩,⟨1400458038710,1400458096586⟩,⟨0,0⟩,⟨-10682162304259,-10682162303779⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes10 := centerStep9.proposed :: centerBoxes9
theorem centerAccepted9 : StepValid centerStep9.shape centerBoxes9 centerStep9.proposed := by
  dsimp only [StepValid,centerStep9]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep10 : Instruction 40 := ⟨.add 12 7,⟨⟨986339239526,986339239527⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes11 := centerStep10.proposed :: centerBoxes10
theorem centerAccepted10 : StepValid centerStep10.shape centerBoxes10 centerStep10.proposed := by
  dsimp only [StepValid,centerStep10]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep11 : Instruction 40 := ⟨.log 0,⟨⟨-119430089600,-119430089536⟩,⟨-1225669395649,-1225669395647⟩,⟨0,0⟩,⟨-1366302483285,-1366302483280⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes12 := centerStep11.proposed :: centerBoxes11
theorem centerAccepted11 : StepValid centerStep11.shape centerBoxes11 centerStep11.proposed := by
  dsimp only [StepValid,centerStep11]
  exact ⟨by decide,by decide,lc1,by decide⟩
noncomputable def centerStep12 : Instruction 40 := ⟨.mul 1 0,⟨⟨-107137187800,-107137187741⟩,⟨-980081538242,-980081538174⟩,⟨0,0⟩,⟨1225669395643,1225669395653⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes13 := centerStep12.proposed :: centerBoxes12
theorem centerAccepted12 : StepValid centerStep12.shape centerBoxes12 centerStep12.proposed := by
  dsimp only [StepValid,centerStep12]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep13 : Instruction 40 := ⟨.neg 0,⟨⟨107137187741,107137187800⟩,⟨980081538174,980081538242⟩,⟨0,0⟩,⟨-1225669395653,-1225669395643⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes14 := centerStep13.proposed :: centerBoxes13
theorem centerAccepted13 : StepValid centerStep13.shape centerBoxes13 centerStep13.proposed := by
  dsimp only [StepValid,centerStep13]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep14 : Instruction 40 := ⟨.add 4 0,⟨⟨364458284271,364458290288⟩,⟨2380539576884,2380539634828⟩,⟨0,0⟩,⟨-11907831699912,-11907831699422⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes15 := centerStep14.proposed :: centerBoxes14
theorem centerAccepted14 : StepValid centerStep14.shape centerBoxes14 centerStep14.proposed := by
  dsimp only [StepValid,centerStep14]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2073439125696,-2073439086976⟩,⟨6357078571585,6357078571669⟩,⟨2877742314858,2877742314901⟩,⟨-36754907311091,-36754907310120⟩,⟨-23885764607098,-23885764606548⟩,⟨-7531890179025,-7531890178806⟩⟩⟩
noncomputable def centerBoxes16 := centerStep15.proposed :: centerBoxes15
theorem centerAccepted15 : StepValid centerStep15.shape centerBoxes15 centerStep15.proposed := by
  dsimp only [StepValid,centerStep15]
  exact ⟨by decide,by decide,lc2,by decide⟩
noncomputable def centerStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-314562270456,-314562264577⟩,⟨-854278983052,-854278949061⟩,⟨-386717695959,-386717680569⟩,⟨5576101535978,5576101536353⟩,⟨3498134634118,3498134673048⟩,⟨1142666040220,1142666040308⟩⟩⟩
noncomputable def centerBoxes17 := centerStep16.proposed :: centerBoxes16
theorem centerAccepted16 : StepValid centerStep16.shape centerBoxes16 centerStep16.proposed := by
  dsimp only [StepValid,centerStep16]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep17 : Instruction 40 := ⟨.neg 0,⟨⟨314562264577,314562270456⟩,⟨854278949061,854278983052⟩,⟨386717680569,386717695959⟩,⟨-5576101536353,-5576101535978⟩,⟨-3498134673048,-3498134634118⟩,⟨-1142666040308,-1142666040220⟩⟩⟩
noncomputable def centerBoxes18 := centerStep17.proposed :: centerBoxes17
theorem centerAccepted17 : StepValid centerStep17.shape centerBoxes17 centerStep17.proposed := by
  dsimp only [StepValid,centerStep17]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-166807344252,-166807344250⟩,⟨-964434906317,-964434906316⟩,⟨-436583425639,-436583425638⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes19 := centerStep18.proposed :: centerBoxes18
theorem centerAccepted18 : StepValid centerStep18.shape centerBoxes18 centerStep18.proposed := by
  dsimp only [StepValid,centerStep18]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨932704283524,932704283526⟩,⟨-964434906317,-964434906316⟩,⟨-436583425639,-436583425638⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes20 := centerStep19.proposed :: centerBoxes19
theorem centerAccepted19 : StepValid centerStep19.shape centerBoxes19 centerStep19.proposed := by
  dsimp only [StepValid,centerStep19]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep20 : Instruction 40 := ⟨.log 0,⟨⟨-180906152448,-180906152384⟩,⟨-1136917040547,-1136917040541⟩,⟨-514663180458,-514663180454⟩,⟨-1175594986385,-1175594986373⟩,⟨763979211813,763979211824⟩,⟨-240905309801,-240905309797⟩⟩⟩
noncomputable def centerBoxes21 := centerStep20.proposed :: centerBoxes20
theorem centerAccepted20 : StepValid centerStep20.shape centerBoxes20 centerStep20.proposed := by
  dsimp only [StepValid,centerStep20]
  exact ⟨by decide,by decide,lc3,by decide⟩
noncomputable def centerStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-153460808456,-153460808400⟩,⟨-805753357423,-805753357358⟩,⟨-364750963181,-364750963150⟩,⟨997245005667,997245005694⟩,⟨1370041479893,1370041479978⟩,⟨204357469891,204357469900⟩⟩⟩
noncomputable def centerBoxes22 := centerStep21.proposed :: centerBoxes21
theorem centerAccepted21 : StepValid centerStep21.shape centerBoxes21 centerStep21.proposed := by
  dsimp only [StepValid,centerStep21]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep22 : Instruction 40 := ⟨.neg 0,⟨⟨153460808400,153460808456⟩,⟨805753357358,805753357423⟩,⟨364750963150,364750963181⟩,⟨-997245005694,-997245005667⟩,⟨-1370041479978,-1370041479893⟩,⟨-204357469900,-204357469891⟩⟩⟩
noncomputable def centerBoxes23 := centerStep22.proposed :: centerBoxes22
theorem centerAccepted22 : StepValid centerStep22.shape centerBoxes22 centerStep22.proposed := by
  dsimp only [StepValid,centerStep22]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨468023072977,468023078912⟩,⟨1660032306419,1660032340475⟩,⟨751468643719,751468659140⟩,⟨-6573346542047,-6573346541645⟩,⟨-4868176153026,-4868176114011⟩,⟨-1347023510208,-1347023510111⟩⟩⟩
noncomputable def centerBoxes24 := centerStep23.proposed :: centerBoxes23
theorem centerAccepted23 : StepValid centerStep23.shape centerBoxes23 centerStep23.proposed := by
  dsimp only [StepValid,centerStep23]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨832481357248,832481369200⟩,⟨4040571883303,4040571975303⟩,⟨751468643719,751468659140⟩,⟨-18481178241959,-18481178241067⟩,⟨-4868176153026,-4868176114011⟩,⟨-1347023510208,-1347023510111⟩⟩⟩
noncomputable def centerBoxes25 := centerStep24.proposed :: centerBoxes24
theorem centerAccepted24 : StepValid centerStep24.shape centerBoxes24 centerStep24.proposed := by
  dsimp only [StepValid,centerStep24]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨107269912000,107269912006⟩,⟨-270153442920,-270153442918⟩,⟨873166851276,873166851278⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes26 := centerStep25.proposed :: centerBoxes25
theorem centerAccepted25 : StepValid centerStep25.shape centerBoxes25 centerStep25.proposed := by
  dsimp only [StepValid,centerStep25]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep26 : Instruction 40 := ⟨.inv 0,⟨⟨11269943239507,11269943240139⟩,⟨28382739490573,28382739493967⟩,⟨-91736262942722,-91736262932222⟩,⟨142960773425329,142960773451498⟩,⟨-231032792104329,-231032791996200⟩,⟨1493448859133377,1493448859391472⟩⟩⟩
noncomputable def centerBoxes27 := centerStep26.proposed :: centerBoxes26
theorem centerAccepted26 : StepValid centerStep26.shape centerBoxes26 centerStep26.proposed := by
  dsimp only [StepValid,centerStep26]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨8532895339278,8532895462265⟩,⟨62905307707752,62905308964170⟩,⟨-61754436336621,-61754435172973⟩,⟨127415976030548,127415982398867⟩,⟨-542543419618682,-542543408507838⟩,⟨991543494558290,991543513577296⟩⟩⟩
noncomputable def centerBoxes28 := centerStep27.proposed :: centerBoxes27
theorem centerAccepted27 : StepValid centerStep27.shape centerBoxes27 centerStep27.proposed := by
  dsimp only [StepValid,centerStep27]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep28 : Instruction 40 := ⟨.contact 0,⟨⟨97644399616,97644532992⟩,⟨-711679723021,-711677735390⟩,⟨698657365741,698659316218⟩,⟨8873403643138,8873451936491⟩,⟨-3988201737554,-3988141188038⟩,⟨-1276887246137,-1276813326786⟩⟩⟩
noncomputable def centerBoxes29 := centerStep28.proposed :: centerBoxes28
theorem centerAccepted28 : StepValid centerStep28.shape centerBoxes28 centerStep28.proposed := by
  dsimp only [StepValid,centerStep28]
  exact ⟨by decide,by decide,(⟨⟨97644399616,97644532992⟩,⟨-12439333716,-12439299223⟩,⟨3151310250,3151323635⟩⟩ : DyadicJetEnclosure 40),brcenter28_jet,by decide⟩
noncomputable def centerStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes30 := centerStep29.proposed :: centerBoxes29
theorem centerAccepted29 : StepValid centerStep29.shape centerBoxes29 centerStep29.proposed := by
  dsimp only [StepValid,centerStep29]
  exact ⟨by decide,by decide,lc4,by decide⟩
noncomputable def centerStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1197156027392,1197156160768⟩,⟨-711679723021,-711677735390⟩,⟨698657365741,698659316218⟩,⟨8873403643138,8873451936491⟩,⟨-3988201737554,-3988141188038⟩,⟨-1276887246137,-1276813326786⟩⟩⟩
noncomputable def centerBoxes31 := centerStep30.proposed :: centerBoxes30
theorem centerAccepted30 : StepValid centerStep30.shape centerBoxes30 centerStep30.proposed := by
  dsimp only [StepValid,centerStep30]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep31 : Instruction 40 := ⟨.log 0,⟨⟨93549374272,93549496832⟩,⟨-653632536454,-653630638118⟩,⟨641672258505,641674121384⟩,⟨7761087244696,7761134764061⟩,⟨-3281452279868,-3281394045604⟩,⟨-1547220191010,-1547149995792⟩⟩⟩
noncomputable def centerBoxes32 := centerStep31.proposed :: centerBoxes31
theorem centerAccepted31 : StepValid centerStep31.shape centerBoxes31 centerStep31.proposed := by
  dsimp only [StepValid,centerStep31]
  exact ⟨by decide,by decide,lc13,by decide⟩
noncomputable def centerStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨101857219550,101857364343⟩,⟨-772231485726,-772229091070⟩,⟨758100915185,758103265171⟩,⟨10051446658703,10051509258275⟩,⟨-4742867532403,-4742793400675⟩,⟨-977796156376,-977708464016⟩⟩⟩
noncomputable def centerBoxes33 := centerStep32.proposed :: centerBoxes32
theorem centerAccepted32 : StepValid centerStep32.shape centerBoxes32 centerStep32.proposed := by
  dsimp only [StepValid,centerStep32]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-97644532992,-97644399616⟩,⟨711677735390,711679723021⟩,⟨-698659316218,-698657365741⟩,⟨-8873451936491,-8873403643138⟩,⟨3988141188038,3988201737554⟩,⟨1276813326786,1276887246137⟩⟩⟩
noncomputable def centerBoxes34 := centerStep33.proposed :: centerBoxes33
theorem centerAccepted33 : StepValid centerStep33.shape centerBoxes33 centerStep33.proposed := by
  dsimp only [StepValid,centerStep33]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1001867094784,1001867228160⟩,⟨711677735390,711679723021⟩,⟨-698659316218,-698657365741⟩,⟨-8873451936491,-8873403643138⟩,⟨3988141188038,3988201737554⟩,⟨1276813326786,1276887246137⟩⟩⟩
noncomputable def centerBoxes35 := centerStep34.proposed :: centerBoxes34
theorem centerAccepted34 : StepValid centerStep34.shape centerBoxes34 centerStep34.proposed := by
  dsimp only [StepValid,centerStep34]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep35 : Instruction 40 := ⟨.log 0,⟨⟨-102255408832,-102255262400⟩,⟨781039566218,781041851547⟩,⟨-766752442550,-766750199898⟩,⟨-10293097043461,-10293039500102⟩,⟨4921497097360,4921567317630⟩,⟨866554236289,866638674413⟩⟩⟩
noncomputable def centerBoxes36 := centerStep35.proposed :: centerBoxes35
theorem centerAccepted35 : StepValid centerStep35.shape centerBoxes35 centerStep35.proposed := by
  dsimp only [StepValid,centerStep35]
  exact ⟨by decide,by decide,lc14,by decide⟩
noncomputable def centerStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-93174406185,-93174260352⟩,⟨645490890822,645493347575⟩,⟨-633683841481,-633681430537⟩,⟨-7542682803190,-7542617666142⟩,⟨3120936951619,3121013370492⟩,⟨1645271274793,1645360934368⟩⟩⟩
noncomputable def centerBoxes37 := centerStep36.proposed :: centerBoxes36
theorem centerAccepted36 : StepValid centerStep36.shape centerBoxes36 centerStep36.proposed := by
  dsimp only [StepValid,centerStep36]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨8682813365,8683103991⟩,⟨-126740594904,-126735743495⟩,⟨124417073704,124421834634⟩,⟨2508763855513,2508891592133⟩,⟨-1621930580784,-1621780030183⟩,⟨667475118417,667652470352⟩⟩⟩
noncomputable def centerBoxes38 := centerStep37.proposed :: centerBoxes37
theorem centerAccepted37 : StepValid centerStep37.shape centerBoxes37 centerStep37.proposed := by
  dsimp only [StepValid,centerStep37]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨4341406682,4341551996⟩,⟨-63370297452,-63367871747⟩,⟨62208536852,62210917317⟩,⟨1254381927756,1254445796067⟩,⟨-810965290392,-810890015091⟩,⟨333737559208,333826235176⟩⟩⟩
noncomputable def centerBoxes39 := centerStep38.proposed :: centerBoxes38
theorem centerAccepted38 : StepValid centerStep38.shape centerBoxes38 centerStep38.proposed := by
  dsimp only [StepValid,centerStep38]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-4341551996,-4341406682⟩,⟨63367871747,63370297452⟩,⟨-62210917317,-62208536852⟩,⟨-1254445796067,-1254381927756⟩,⟨810890015091,810965290392⟩,⟨-333826235176,-333737559208⟩⟩⟩
noncomputable def centerBoxes40 := centerStep39.proposed :: centerBoxes39
theorem centerAccepted39 : StepValid centerStep39.shape centerBoxes39 centerStep39.proposed := by
  dsimp only [StepValid,centerStep39]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨757781831620,757781996198⟩,⟨63367871747,63370297452⟩,⟨-62210917317,-62208536852⟩,⟨-1254445796067,-1254381927756⟩,⟨810890015091,810965290392⟩,⟨-333826235176,-333737559208⟩⟩⟩
noncomputable def centerBoxes41 := centerStep40.proposed :: centerBoxes40
theorem centerAccepted40 : StepValid centerStep40.shape centerBoxes40 centerStep40.proposed := by
  dsimp only [StepValid,centerStep40]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨8671512456,8671536147⟩,⟨-126404546236,-126404020542⟩,⟨124091418938,124091934874⟩,⟨2497333062518,2497348939007⟩,⟨-1612802888838,-1612786115862⟩,⟨661095429443,661113825887⟩⟩⟩
noncomputable def centerBoxes42 := centerStep41.proposed :: centerBoxes41
theorem centerAccepted41 : StepValid centerStep41.shape centerBoxes41 centerStep41.proposed := by
  dsimp only [StepValid,centerStep41]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-8671536147,-8671512456⟩,⟨126404020542,126404546236⟩,⟨-124091934874,-124091418938⟩,⟨-2497348939007,-2497333062518⟩,⟨1612786115862,1612802888838⟩,⟨-661113825887,-661095429443⟩⟩⟩
noncomputable def centerBoxes43 := centerStep42.proposed :: centerBoxes42
theorem centerAccepted42 : StepValid centerStep42.shape centerBoxes42 centerStep42.proposed := by
  dsimp only [StepValid,centerStep42]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1090840091629,1090840115320⟩,⟨126404020542,126404546236⟩,⟨-124091934874,-124091418938⟩,⟨-2497348939007,-2497333062518⟩,⟨1612786115862,1612802888838⟩,⟨-661113825887,-661095429443⟩⟩⟩
noncomputable def centerBoxes44 := centerStep43.proposed :: centerBoxes43
theorem centerAccepted43 : StepValid centerStep43.shape centerBoxes43 centerStep43.proposed := by
  dsimp only [StepValid,centerStep43]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep44 : Instruction 40 := ⟨.log 0,⟨⟨-8705912000,-8705888064⟩,⟨127408855277,127409387918⟩,⟨-125078392658,-125077869903⟩,⟨-2531965357815,-2531949177003⟩,⟨1640100513370,1640117576158⟩,⟨-680597976093,-680579299999⟩⟩⟩
noncomputable def centerBoxes45 := centerStep44.proposed :: centerBoxes44
theorem centerAccepted44 : StepValid centerStep44.shape centerBoxes44 centerStep44.proposed := by
  dsimp only [StepValid,centerStep44]
  exact ⟨by decide,by decide,lc11,by decide⟩
noncomputable def centerStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-4352956000,-4352944032⟩,⟨63704427638,63704693959⟩,⟨-62539196329,-62538934951⟩,⟨-1265982678908,-1265974588501⟩,⟨820050256685,820058788079⟩,⟨-340298988047,-340289649999⟩⟩⟩
noncomputable def centerBoxes46 := centerStep45.proposed :: centerBoxes45
theorem centerAccepted45 : StepValid centerStep45.shape centerBoxes45 centerStep45.proposed := by
  dsimp only [StepValid,centerStep45]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep46 : Instruction 40 := ⟨.neg 0,⟨⟨4352944032,4352956000⟩,⟨-63704693959,-63704427638⟩,⟨62538934951,62539196329⟩,⟨1265974588501,1265982678908⟩,⟨-820058788079,-820050256685⟩,⟨340289649999,340298988047⟩⟩⟩
noncomputable def centerBoxes47 := centerStep46.proposed :: centerBoxes46
theorem centerAccepted46 : StepValid centerStep46.shape centerBoxes46 centerStep46.proposed := by
  dsimp only [StepValid,centerStep46]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨766476327648,766476358880⟩,⟨-63704693959,-63704427638⟩,⟨62538934951,62539196329⟩,⟨1265974588501,1265982678908⟩,⟨-820058788079,-820050256685⟩,⟨340289649999,340298988047⟩⟩⟩
noncomputable def centerBoxes48 := centerStep47.proposed :: centerBoxes47
theorem centerAccepted47 : StepValid centerStep47.shape centerBoxes47 centerStep47.proposed := by
  dsimp only [StepValid,centerStep47]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes49 := centerStep48.proposed :: centerBoxes48
theorem centerAccepted48 : StepValid centerStep48.shape centerBoxes48 centerStep48.proposed := by
  dsimp only [StepValid,centerStep48]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes50 := centerStep49.proposed :: centerBoxes49
theorem centerAccepted49 : StepValid centerStep49.shape centerBoxes49 centerStep49.proposed := by
  dsimp only [StepValid,centerStep49]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272710022907,272710028830⟩,⟨31601005135,31601136559⟩,⟨-31022983719,-31022854734⟩,⟨-624337234752,-624333265629⟩,⟨403196528965,403200722210⟩,⟨-165278456472,-165273857360⟩⟩⟩
noncomputable def centerBoxes51 := centerStep50.proposed :: centerBoxes50
theorem centerAccepted50 : StepValid centerStep50.shape centerBoxes50 centerStep50.proposed := by
  dsimp only [StepValid,centerStep50]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1532952655296,1532952717760⟩,⟨-127409387918,-127408855276⟩,⟨125077869902,125078392658⟩,⟨2531949177002,2531965357816⟩,⟨-1640117576158,-1640100513370⟩,⟨680579299998,680597976094⟩⟩⟩
noncomputable def centerBoxes52 := centerStep51.proposed :: centerBoxes51
theorem centerAccepted51 : StepValid centerStep51.shape centerBoxes51 centerStep51.proposed := by
  dsimp only [StepValid,centerStep51]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1206672686394,1206672847036⟩,⟨-857164190767,-857161568590⟩,⟨841479526119,841482099371⟩,⟨11905109863125,11905178162936⟩,⟨-5998985565369,-5998904205274⟩,⟨-364293416750,-364196955397⟩⟩⟩
noncomputable def centerBoxes53 := centerStep52.proposed :: centerBoxes52
theorem centerAccepted52 : StepValid centerStep52.shape centerBoxes52 centerStep52.proposed := by
  dsimp only [StepValid,centerStep52]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1313833745012,1313834066296⟩,⟨-1714328381534,-1714323137181⟩,⟨1682959052239,1682964198742⟩,⟨23810219726256,23810356325867⟩,⟨-11997971130736,-11997808410550⟩,⟨-728586691134,-728394053161⟩⟩⟩
noncomputable def centerBoxes54 := centerStep53.proposed :: centerBoxes53
theorem centerAccepted53 : StepValid centerStep53.shape centerBoxes53 centerStep53.proposed := by
  dsimp only [StepValid,centerStep53]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep54 : Instruction 40 := ⟨.log 0,⟨⟨195804636736,195804905664⟩,⟨-1434674666016,-1434669926323⟩,⟨1408422185476,1408426836862⟩,⟨18054113497069,18054245055277⟩,⟨-8203030756257,-8202879984232⟩,⟨-2413868188252,-2413694909289⟩⟩⟩
noncomputable def centerBoxes55 := centerStep54.proposed :: centerBoxes54
theorem centerAccepted54 : StepValid centerStep54.shape centerBoxes54 centerStep54.proposed := by
  dsimp only [StepValid,centerStep54]
  exact ⟨by decide,by decide,lc16,by decide⟩
noncomputable def centerStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨67296379700,67296486240⟩,⟨-484861232848,-484859533340⟩,⟨475988874602,475990542395⟩,⟨5922097971053,5922141776369⟩,⟨-2596119651818,-2596067233829⟩,⟨-988736198489,-988673900768⟩⟩⟩
noncomputable def centerBoxes56 := centerStep55.proposed :: centerBoxes55
theorem centerAccepted55 : StepValid centerStep55.shape centerBoxes55 centerStep55.proposed := by
  dsimp only [StepValid,centerStep55]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380215673195,380215696947⟩,⟨12457373376,12457691203⟩,⟨-12229773747,-12229461818⟩,⟨-249787358996,-249777701707⟩,⟨162535662658,162545832682⟩,⟨-68688561826,-68677445583⟩⟩⟩
noncomputable def centerBoxes57 := centerStep56.proposed :: centerBoxes56
theorem centerAccepted56 : StepValid centerStep56.shape centerBoxes56 centerStep56.proposed := by
  dsimp only [StepValid,centerStep56]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3179578931963,3179579130592⟩,⟨-104178280269,-104175609402⟩,⟨102269683913,102272305219⟩,⟨2095608974971,2095690345286⟩,⟨-1366002318081,-1365916757579⟩,⟨580898598450,580991967383⟩⟩⟩
noncomputable def centerBoxes58 := centerStep57.proposed :: centerBoxes57
theorem centerAccepted57 : StepValid centerStep57.shape centerBoxes57 centerStep57.proposed := by
  dsimp only [StepValid,centerStep57]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨194608356734,194608676985⟩,⟨-1408503057430,-1408497881616⟩,⟨1382728966758,1382734046037⟩,⟨17345724621720,17345860229262⟩,⟨-7681292821664,-7681132772353⟩,⟨-2735136282559,-2734947599907⟩⟩⟩
noncomputable def centerBoxes59 := centerStep58.proposed :: centerBoxes58
theorem centerAccepted58 : StepValid centerStep58.shape centerBoxes58 centerStep58.proposed := by
  dsimp only [StepValid,centerStep58]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨390412993470,390413582649⟩,⟨-2843177723446,-2843167807939⟩,⟨2791151152234,2791160882899⟩,⟨35399838118789,35400105284539⟩,⟨-15884323577921,-15884012756585⟩,⟨-5149004470811,-5148642509196⟩⟩⟩
noncomputable def centerBoxes60 := centerStep59.proposed :: centerBoxes59
theorem centerAccepted59 : StepValid centerStep59.shape centerBoxes59 centerStep59.proposed := by
  dsimp only [StepValid,centerStep59]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨522262147872,522262374727⟩,⟨87346092038,87349454594⟩,⟨-85751368006,-85748068154⟩,⟨-1721820721827,-1721731751179⟩,⟨1110557416800,1110661967716⟩,⟨-453105910890,-452983041509⟩⟩⟩
noncomputable def centerBoxes61 := centerStep60.proposed :: centerBoxes60
theorem centerAccepted60 : StepValid centerStep60.shape centerBoxes60 centerStep60.proposed := by
  dsimp only [StepValid,centerStep60]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨359942320756,359942555279⟩,⟨90298201405,90301697223⟩,⟨-88649598399,-88646167764⟩,⟨-1772463940313,-1772370995210⟩,⟨1140678446058,1140787350059⟩,⟨-461142790536,-461015107115⟩⟩⟩
noncomputable def centerBoxes62 := centerStep61.proposed :: centerBoxes61
theorem centerAccepted61 : StepValid centerStep61.shape centerBoxes61 centerStep61.proposed := by
  dsimp only [StepValid,centerStep61]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨719884641512,719885110558⟩,⟨180596402810,180603394446⟩,⟨-177299196798,-177292335528⟩,⟨-3544927880626,-3544741990420⟩,⟨2281356892116,2281574700118⟩,⟨-922285581072,-922030214230⟩⟩⟩
noncomputable def centerBoxes63 := centerStep62.proposed :: centerBoxes62
theorem centerAccepted62 : StepValid centerStep62.shape centerBoxes62 centerStep62.proposed := by
  dsimp only [StepValid,centerStep62]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1524281119149,1524281205304⟩,⟨-1005367376,-1004309040⟩,⟨985935028,986973720⟩,⟨34600237995,34632295298⟩,⟨-27331460296,-27297624532⟩,⟨19465474111,19502546651⟩⟩⟩
noncomputable def centerBoxes64 := centerStep63.proposed :: centerBoxes63
theorem centerAccepted63 : StepValid centerStep63.shape centerBoxes63 centerStep63.proposed := by
  dsimp only [StepValid,centerStep63]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨997994508927,997995215587⟩,⟨249707170936,249717571129⟩,⟨-245148907117,-245138700783⟩,⟨-4892100976753,-4891821630482⟩,⟨3145132575800,3145457226192⟩,⟨-1266161835334,-1265783113313⟩⟩⟩
noncomputable def centerBoxes65 := centerStep64.proposed :: centerBoxes64
theorem centerAccepted64 : StepValid centerStep64.shape centerBoxes64 centerStep64.proposed := by
  dsimp only [StepValid,centerStep64]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67639809089,67639812028⟩,⟨15675888488,15675954024⟩,⟨-15389157460,-15389093140⟩,⟨-307890153207,-307888162457⟩,⟨198225048924,198227148190⟩,⟨-80236850617,-80234552855⟩⟩⟩
noncomputable def centerBoxes66 := centerStep65.proposed :: centerBoxes65
theorem centerAccepted65 : StepValid centerStep65.shape centerBoxes65 centerStep65.proposed := by
  dsimp only [StepValid,centerStep65]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨51212628090,51212631051⟩,⟨260436896242,260436962494⟩,⟨34577177506,34577229331⟩,⟨-1254827229884,-1254825185511⟩,⟨-195236609069,-195234719398⟩,⟨-164652228100,-164650395545⟩⟩⟩
noncomputable def centerBoxes67 := centerStep66.proposed :: centerBoxes66
theorem centerAccepted66 : StepValid centerStep66.shape centerBoxes66 centerStep66.proposed := by
  dsimp only [StepValid,centerStep66]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2137261475017,2137261649194⟩,⟨-355271490622,-355269990910⟩,⟨348770213868,348771685746⟩,⟨7089677147382,7089722800936⟩,⟨-4602332150660,-4602284143668⟩,⟨1926201218539,1926253610629⟩⟩⟩
noncomputable def centerBoxes68 := centerStep67.proposed :: centerBoxes67
theorem centerAccepted67 : StepValid centerStep67.shape centerBoxes67 centerStep67.proposed := by
  dsimp only [StepValid,centerStep67]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2979796275384,2979796639644⟩,⟨-742985862996,-742982696346⟩,⟨729389592520,729392700408⟩,⟨14888524607784,14888621206900⟩,⟨-9685565190094,-9685463890717⟩,⟨4087813124028,4087923356611⟩⟩⟩
noncomputable def centerBoxes69 := centerStep68.proposed :: centerBoxes68
theorem centerAccepted68 : StepValid centerStep68.shape centerBoxes68 centerStep68.proposed := by
  dsimp only [StepValid,centerStep68]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨138791800450,138791825442⟩,⟨671205846189,671206261517⟩,⟨127681144185,127681442815⟩,⟨-3059223174265,-3059211088939⟩,⟨-830840780681,-830829935709⟩,⟨-209949608651,-209939178065⟩⟩⟩
noncomputable def centerBoxes70 := centerStep69.proposed :: centerBoxes69
theorem centerAccepted69 : StepValid centerStep69.shape centerBoxes69 centerStep69.proposed := by
  dsimp only [StepValid,centerStep69]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8710353190936,8710354759395⟩,⟨-42123847630658,-42123806394995⟩,⟨-8013086216219,-8013064588871⟩,⟨599417862236831,599419414144390⟩,⟨129644910427576,129645880914920⟩,⟨27918639210136,27919375491625⟩⟩⟩
noncomputable def centerBoxes71 := centerStep70.proposed :: centerBoxes70
theorem centerAccepted70 : StepValid centerStep70.shape centerBoxes70 centerStep70.proposed := by
  dsimp only [StepValid,centerStep70]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨7906132537181,7906139559002⟩,⟨-36256424886552,-36256277638240⟩,⟨-9215323785375,-9215217800335⟩,⟨486184644801090,486189474258578⟩,⟨150162387425671,150166408925992⟩,⟨18883433172117,18887279875182⟩⟩⟩
noncomputable def centerBoxes72 := centerStep71.proposed :: centerBoxes71
theorem centerAccepted71 : StepValid centerStep71.shape centerBoxes71 centerStep71.proposed := by
  dsimp only [StepValid,centerStep71]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨15812265074362,15812279118004⟩,⟨-72512849773104,-72512555276480⟩,⟨-18430647570750,-18430435600670⟩,⟨972369289602180,972378948517156⟩,⟨300324774851342,300332817851984⟩,⟨37766866344234,37774559750364⟩⟩⟩
noncomputable def centerBoxes73 := centerStep72.proposed :: centerBoxes72
theorem centerAccepted72 : StepValid centerStep72.shape centerBoxes72 centerStep72.proposed := by
  dsimp only [StepValid,centerStep72]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10682162303971,10682162304067⟩,⟨-103781159387318,-103781159385452⟩,⟨0,0⟩,⟨2016544728848532,2016544728902914⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes74 := centerStep73.proposed :: centerBoxes73
theorem centerAccepted73 : StepValid centerStep73.shape centerBoxes73 centerStep73.proposed := by
  dsimp only [StepValid,centerStep73]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9582650676195,9582650676291⟩,⟨-103781159387318,-103781159385452⟩,⟨0,0⟩,⟨2016544728848550,2016544728902902⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes75 := centerStep74.proposed :: centerBoxes74
theorem centerAccepted74 : StepValid centerStep74.shape centerBoxes74 centerStep74.proposed := by
  dsimp only [StepValid,centerStep74]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep75 : Instruction 40 := ⟨.log 0,⟨⟨2380539576896,2380539634752⟩,⟨-11907831699843,-11907831699439⟩,⟨0,0⟩,⟨102414856889766,102414856913318⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes76 := centerStep75.proposed :: centerBoxes75
theorem centerAccepted75 : StepValid centerStep75.shape centerBoxes75 centerStep75.proposed := by
  dsimp only [StepValid,centerStep75]
  exact ⟨by decide,by decide,lc17,by decide⟩
noncomputable def centerStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7247437605554,7247437605642⟩,⟨-41902722207247,-41902722206184⟩,⟨-18968656033719,-18968656033214⟩,⟨484540391749799,484540391768467⟩,⟨267114797177265,267114797187152⟩,⟨99293000171720,99293000175795⟩⟩⟩
noncomputable def centerBoxes77 := centerStep76.proposed :: centerBoxes76
theorem centerAccepted76 : StepValid centerStep76.shape centerBoxes76 centerStep76.proposed := by
  dsimp only [StepValid,centerStep76]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6147925977778,6147925977866⟩,⟨-41902722207247,-41902722206184⟩,⟨-18968656033720,-18968656033213⟩,⟨484540391749803,484540391768463⟩,⟨267114797177265,267114797187151⟩,⟨99293000171720,99293000175795⟩⟩⟩
noncomputable def centerBoxes78 := centerStep77.proposed :: centerBoxes77
theorem centerAccepted77 : StepValid centerStep77.shape centerBoxes77 centerStep77.proposed := by
  dsimp only [StepValid,centerStep77]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep78 : Instruction 40 := ⟨.log 0,⟨⟨1892532934592,1892532973184⟩,⟨-7493995612337,-7493995611993⟩,⟨-3392405495413,-3392405495252⟩,⟨35579312318511,35579312329139⟩,⟨24649743815816,24649743821091⟩,⟨7290984867912,7290984870163⟩⟩⟩
noncomputable def centerBoxes79 := centerStep78.proposed :: centerBoxes78
theorem centerAccepted78 : StepValid centerStep78.shape centerBoxes78 centerStep78.proposed := by
  dsimp only [StepValid,centerStep78]
  exact ⟨by decide,by decide,lc18,by decide⟩
noncomputable def centerStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨101523589692,101523589694⟩,⟨873166851276,873166851278⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes80 := centerStep79.proposed :: centerBoxes79
theorem centerAccepted79 : StepValid centerStep79.shape centerBoxes79 centerStep79.proposed := by
  dsimp only [StepValid,centerStep79]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨141500936029,141500936032⟩,⟨671805303566,671805303573⟩,⟨304114937018,304114937023⟩,⟨-1691905142294,-1691905142289⟩,⟨-1531793878552,-1531793878544⟩,⟨-346708634503,-346708634500⟩⟩⟩
noncomputable def centerBoxes81 := centerStep80.proposed :: centerBoxes80
theorem centerAccepted80 : StepValid centerStep80.shape centerBoxes80 centerStep80.proposed := by
  dsimp only [StepValid,centerStep80]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4273072511488,4273072607936⟩,⟨-19401827312180,-19401827311432⟩,⟨-3392405495413,-3392405495252⟩,⟨137994169208277,137994169242457⟩,⟨24649743815816,24649743821091⟩,⟨7290984867912,7290984870163⟩⟩⟩
noncomputable def centerBoxes82 := centerStep81.proposed :: centerBoxes81
theorem centerAccepted81 : StepValid centerStep81.shape centerBoxes81 centerStep81.proposed := by
  dsimp only [StepValid,centerStep81]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨780825986940,780827165298⟩,⟨-5686355446892,-5686335615878⟩,⟨5582302304468,5582321765798⟩,⟨70799676237578,70800210569078⟩,⟨-31768647155842,-31768025513170⟩,⟨-10298008941622,-10297285018392⟩⟩⟩
noncomputable def centerBoxes83 := centerStep82.proposed :: centerBoxes82
theorem centerAccepted82 : StepValid centerStep82.shape centerBoxes82 centerStep82.proposed := by
  dsimp only [StepValid,centerStep82]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5053898498428,5053899773234⟩,⟨-25088182759072,-25088162927310⟩,⟨2189896809055,2189916270546⟩,⟨208793845445855,208794379811535⟩,⟨-7118903340026,-7118281692079⟩,⟨-3007024073710,-3006300148229⟩⟩⟩
noncomputable def centerBoxes84 := centerStep83.proposed :: centerBoxes83
theorem centerAccepted83 : StepValid centerStep83.shape centerBoxes83 centerStep83.proposed := by
  dsimp only [StepValid,centerStep83]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨466652561498,466652679218⟩,⟨1696984569153,1696987412753⟩,⟨202204487423,202206284408⟩,⟨-30675875246165,-30675791856920⟩,⟨1081760892354,1081833747501⟩,⟨-277654069814,-277587226027⟩⟩⟩
noncomputable def centerBoxes85 := centerStep84.proposed :: centerBoxes84
theorem centerAccepted84 : StepValid centerStep84.shape centerBoxes84 centerStep84.proposed := by
  dsimp only [StepValid,centerStep84]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep85 : Instruction 40 := ⟨.mul 88 85,⟨⟨226344776498,226344776500⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes86 := centerStep85.proposed :: centerBoxes85
theorem centerAccepted85 : StepValid centerStep85.shape centerBoxes85 centerStep85.proposed := by
  dsimp only [StepValid,centerStep85]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep86 : Instruction 40 := ⟨.neg 0,⟨⟨-226344776500,-226344776498⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes87 := centerStep86.proposed :: centerBoxes86
theorem centerAccepted86 : StepValid centerStep86.shape centerBoxes86 centerStep86.proposed := by
  dsimp only [StepValid,centerStep86]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep87 : Instruction 40 := ⟨.add 89 0,⟨⟨873166851276,873166851278⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes88 := centerStep87.proposed :: centerBoxes87
theorem centerAccepted87 : StepValid centerStep87.shape centerBoxes87 centerStep87.proposed := by
  dsimp only [StepValid,centerStep87]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep88 : Instruction 40 := ⟨.mul 12 0,⟨⟨1890483187431,1890483233382⟩,⟨-14217572178026,-14217572061970⟩,⟨0,0⟩,⟨128963125257405,128963125277912⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes89 := centerStep88.proposed :: centerBoxes88
theorem centerAccepted88 : StepValid centerStep88.shape centerBoxes88 centerStep88.proposed := by
  dsimp only [StepValid,centerStep88]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep89 : Instruction 40 := ⟨.neg 91,⟨⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes90 := centerStep89.proposed :: centerBoxes89
theorem centerAccepted89 : StepValid centerStep89.shape centerBoxes89 centerStep89.proposed := by
  dsimp only [StepValid,centerStep89]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep90 : Instruction 40 := ⟨.add 1 0,⟨⟨790971559655,790971605606⟩,⟨-14217572178026,-14217572061970⟩,⟨0,0⟩,⟨128963125257405,128963125277912⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes91 := centerStep90.proposed :: centerBoxes90
theorem centerAccepted90 : StepValid centerStep90.shape centerBoxes90 centerStep90.proposed := by
  dsimp only [StepValid,centerStep90]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨38584152934,38584155179⟩,⟨-790715339001,-790715327653⟩,⟨314071324370,314071342618⟩,⟨9784214481695,9784214511590⟩,⟨-6436347433334,-6436347341287⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes92 := centerStep91.proposed :: centerBoxes91
theorem centerAccepted91 : StepValid centerStep91.shape centerBoxes91 centerStep91.proposed := by
  dsimp only [StepValid,centerStep91]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨505236714432,505236834397⟩,⟨906269230152,906272085100⟩,⟨516275811793,516277627026⟩,⟨-20891660764470,-20891577345330⟩,⟨-5354586540980,-5354513593786⟩,⟨-277654069814,-277587226027⟩⟩⟩
noncomputable def centerBoxes93 := centerStep92.proposed :: centerBoxes92
theorem centerAccepted92 : StepValid centerStep92.shape centerBoxes92 centerStep92.proposed := by
  dsimp only [StepValid,centerStep92]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep93 : Instruction 40 := ⟨.inv 17,⟨⟨507836879489,507836891833⟩,⟨2540279524621,2540279648204⟩,⟨0,0⟩,⟨3565745386739,3565748309078⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes94 := centerStep93.proposed :: centerBoxes93
theorem centerAccepted93 : StepValid centerStep93.shape centerBoxes93 centerStep93.proposed := by
  dsimp only [StepValid,centerStep93]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨233356182853,233356243935⟩,⟨1585867192785,1585868855541⟩,⟨238454865408,238455709616⟩,⟨-3823203083688,-3823149192330⟩,⟨-1280360913614,-1280322909125⟩,⟨-128241463080,-128210586491⟩⟩⟩
noncomputable def centerBoxes95 := centerStep94.proposed :: centerBoxes94
theorem centerAccepted94 : StepValid centerStep94.shape centerBoxes94 centerStep94.proposed := by
  dsimp only [StepValid,centerStep94]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-780827165298,-780825986940⟩,⟨5686335615878,5686355446892⟩,⟨-5582321765798,-5582302304468⟩,⟨-70800210569078,-70799676237578⟩,⟨31768025513170,31768647155842⟩,⟨10297285018392,10298008941622⟩⟩⟩
noncomputable def centerBoxes96 := centerStep95.proposed :: centerBoxes95
theorem centerAccepted95 : StepValid centerStep95.shape centerBoxes95 centerStep95.proposed := by
  dsimp only [StepValid,centerStep95]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3492245346190,3492246620996⟩,⟨-13715491696302,-13715471864540⟩,⟨-8974727261211,-8974707799720⟩,⟨67193958639199,67194493004879⟩,⟨56417769328986,56418390976933⟩,⟨17588269886304,17588993811785⟩⟩⟩
noncomputable def centerBoxes97 := centerStep96.proposed :: centerBoxes96
theorem centerAccepted96 : StepValid centerStep96.shape centerBoxes96 centerStep96.proposed := by
  dsimp only [StepValid,centerStep96]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨449432250505,449432414576⟩,⟨368667344225,368670675434⟩,⟨-189073338867,-189070481640⟩,⟨-13486735132263,-13486640165849⟩,⟨-6881773600418,-6881674445207⟩,⟨-3802354182841,-3802249849850⟩⟩⟩
noncomputable def centerBoxes98 := centerStep97.proposed :: centerBoxes97
theorem centerAccepted97 : StepValid centerStep97.shape centerBoxes97 centerStep97.proposed := by
  dsimp only [StepValid,centerStep97]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨333614688500,333614688504⟩,⟨1928869812632,1928869812634⟩,⟨873166851276,873166851278⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes99 := centerStep98.proposed :: centerBoxes98
theorem centerAccepted98 : StepValid centerStep98.shape centerBoxes98 centerStep98.proposed := by
  dsimp only [StepValid,centerStep98]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-333614688504,-333614688500⟩,⟨-1928869812634,-1928869812632⟩,⟨-873166851278,-873166851276⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes100 := centerStep99.proposed :: centerBoxes99
theorem centerAccepted99 : StepValid centerStep99.shape centerBoxes99 centerStep99.proposed := by
  dsimp only [StepValid,centerStep99]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨765896939272,765896939276⟩,⟨-1928869812634,-1928869812632⟩,⟨-873166851278,-873166851276⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes101 := centerStep100.proposed :: centerBoxes100
theorem centerAccepted100 : StepValid centerStep100.shape centerBoxes100 centerStep100.proposed := by
  dsimp only [StepValid,centerStep100]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1318299093396,1318299120286⟩,⟨-8540226211905,-8540226143931⟩,⟨-3866016452644,-3866016421867⟩,⟨51077195375992,51077195384760⟩,⟨32858137621074,32858137702601⟩,⟨10466842508042,10466842509906⟩⟩⟩
noncomputable def centerBoxes102 := centerStep101.proposed :: centerBoxes101
theorem centerAccepted101 : StepValid centerStep101.shape centerBoxes101 centerStep101.proposed := by
  dsimp only [StepValid,centerStep101]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1318299120286,-1318299093396⟩,⟨8540226143931,8540226211905⟩,⟨3866016421867,3866016452644⟩,⟨-51077195384760,-51077195375992⟩,⟨-32858137702601,-32858137621074⟩,⟨-10466842509906,-10466842508042⟩⟩⟩
noncomputable def centerBoxes103 := centerStep102.proposed :: centerBoxes102
theorem centerAccepted102 : StepValid centerStep102.shape centerBoxes102 centerStep102.proposed := by
  dsimp only [StepValid,centerStep102]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-218787492510,-218787465620⟩,⟨8540226143931,8540226211905⟩,⟨3866016421867,3866016452644⟩,⟨-51077195384760,-51077195375992⟩,⟨-32858137702601,-32858137621074⟩,⟨-10466842509906,-10466842508042⟩⟩⟩
noncomputable def centerBoxes104 := centerStep103.proposed :: centerBoxes103
theorem centerAccepted103 : StepValid centerStep103.shape centerBoxes103 centerStep103.proposed := by
  dsimp only [StepValid,centerStep103]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-10672608856,-10672607542⟩,⟨443476662450,443476669095⟩,⟨101713001380,101713013572⟩,⟨-4589942038075,-4589942020789⟩,⟨1532068336517,1532068398258⟩,⟨2559580706067,2559580730638⟩⟩⟩
noncomputable def centerBoxes105 := centerStep104.proposed :: centerBoxes104
theorem centerAccepted104 : StepValid centerStep104.shape centerBoxes104 centerStep104.proposed := by
  dsimp only [StepValid,centerStep104]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨438759641649,438759807034⟩,⟨812144006675,812147344529⟩,⟨-87360337487,-87357468068⟩,⟨-18076677170338,-18076582186638⟩,⟨-5349705263901,-5349606046949⟩,⟨-1242773476774,-1242669119212⟩⟩⟩
noncomputable def centerBoxes106 := centerStep105.proposed :: centerBoxes105
theorem centerAccepted105 : StepValid centerStep105.shape centerBoxes105 centerStep105.proposed := by
  dsimp only [StepValid,centerStep105]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-101523589694,-101523589692⟩,⟨-873166851278,-873166851276⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes107 := centerStep106.proposed :: centerBoxes106
theorem centerAccepted106 : StepValid centerStep106.shape centerBoxes106 centerStep106.proposed := by
  dsimp only [StepValid,centerStep106]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4952392615,4952392616⟩,⟨30121365854,30121365859⟩,⟨40312003485,40312003486⟩,⟨-321809736013,-321809736004⟩,⟨245185044806,245185044811⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes108 := centerStep107.proposed :: centerBoxes107
theorem centerAccepted107 : StepValid centerStep107.shape centerBoxes107 centerStep107.proposed := by
  dsimp only [StepValid,centerStep107]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨10722366478,10722366742⟩,⟨11580455740,11580457351⟩,⟨87279040344,87279042468⟩,⟨-887887436820,-887887419533⟩,⟨94263805138,94263818079⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes109 := centerStep108.proposed :: centerBoxes108
theorem centerAccepted108 : StepValid centerStep108.shape centerBoxes108 centerStep108.proposed := by
  dsimp only [StepValid,centerStep108]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1452195645863,1452195666713⟩,⟨-7048447466711,-7048447103826⟩,⟨-1310875638203,-1310875573659⟩,⟨100660271868828,100660278859027⟩,⟨21217193297555,21217194708446⟩,⟨4716388378606,4716388645320⟩⟩⟩
noncomputable def centerBoxes110 := centerStep109.proposed :: centerBoxes109
theorem centerAccepted109 : StepValid centerStep109.shape centerBoxes109 centerStep109.proposed := by
  dsimp only [StepValid,centerStep109]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨14161718275,14161718828⟩,⟨-53440954887,-53440947307⟩,⟨102491460908,102491466314⟩,⟨-339531156065,-339530995758⟩,⟨-241902194510,-241902111752⟩,⟨-162120246702,-162120227656⟩⟩⟩
noncomputable def centerBoxes111 := centerStep110.proposed :: centerBoxes110
theorem centerAccepted110 : StepValid centerStep110.shape centerBoxes110 centerStep110.proposed := by
  dsimp only [StepValid,centerStep110]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-14161718828,-14161718275⟩,⟨53440947307,53440954887⟩,⟨-102491466314,-102491460908⟩,⟨339530995758,339531156065⟩,⟨241902111752,241902194510⟩,⟨162120227656,162120246702⟩⟩⟩
noncomputable def centerBoxes112 := centerStep111.proposed :: centerBoxes111
theorem centerAccepted111 : StepValid centerStep111.shape centerBoxes111 centerStep111.proposed := by
  dsimp only [StepValid,centerStep111]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-115685308522,-115685307967⟩,⟨-819725903971,-819725896389⟩,⟨-102491466314,-102491460908⟩,⟨2538554251310,2538554411617⟩,⟨241902111752,241902194510⟩,⟨162120227656,162120246702⟩⟩⟩
noncomputable def centerBoxes113 := centerStep112.proposed :: centerBoxes112
theorem centerAccepted112 : StepValid centerStep112.shape centerBoxes112 centerStep112.proposed := by
  dsimp only [StepValid,centerStep112]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨92319097052,92319098941⟩,⟨-598063046916,-598063042134⟩,⟨585984700797,585984716141⟩,⟨3576882196744,3576882197460⟩,⟨-3248981874089,-3248981835002⟩,⟨-2338387614238,-2338387613972⟩⟩⟩
noncomputable def centerBoxes114 := centerStep113.proposed :: centerBoxes113
theorem centerAccepted113 : StepValid centerStep113.shape centerBoxes113 centerStep113.proposed := by
  dsimp only [StepValid,centerStep113]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨121931762595,121931766842⟩,⟨-1381714250067,-1381714189830⟩,⟨663881631495,663881670546⟩,⟨20843826491076,20843827775796⟩,⟨-5553103188639,-5553102587913⟩,⟨-4089715568199,-4089715387619⟩⟩⟩
noncomputable def centerBoxes115 := centerStep114.proposed :: centerBoxes114
theorem centerAccepted114 : StepValid centerStep114.shape centerBoxes114 centerStep114.proposed := by
  dsimp only [StepValid,centerStep114]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-121931766842,-121931762595⟩,⟨1381714189830,1381714250067⟩,⟨-663881670546,-663881631495⟩,⟨-20843827775796,-20843826491076⟩,⟨5553102587913,5553103188639⟩,⟨4089715387619,4089715568199⟩⟩⟩
noncomputable def centerBoxes116 := centerStep115.proposed :: centerBoxes115
theorem centerAccepted115 : StepValid centerStep115.shape centerBoxes115 centerStep115.proposed := by
  dsimp only [StepValid,centerStep115]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨977579860934,977579865181⟩,⟨1381714189830,1381714250067⟩,⟨-663881670546,-663881631495⟩,⟨-20843827775796,-20843826491076⟩,⟨5553102587913,5553103188639⟩,⟨4089715387619,4089715568199⟩⟩⟩
noncomputable def centerBoxes117 := centerStep116.proposed :: centerBoxes116
theorem centerAccepted116 : StepValid centerStep116.shape centerBoxes116 centerStep116.proposed := by
  dsimp only [StepValid,centerStep116]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨125809006354,125809006904⟩,⟨775123395596,775123405955⟩,⟨184951895826,184951902035⟩,⟨-2498297999581,-2498297754018⟩,⟨-670735009979,-670734886193⟩,⟨-149183951720,-149183905516⟩⟩⟩
noncomputable def centerBoxes118 := centerStep117.proposed :: centerBoxes117
theorem centerAccepted117 : StepValid centerStep117.shape centerBoxes117 centerStep117.proposed := by
  dsimp only [StepValid,centerStep117]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨12171849884,12171850002⟩,⟨172495206738,172495209162⟩,⟨21567313922,21567315166⟩,⟨688082027231,688082086140⟩,⟨101918657782,101918684920⟩,⟨-15007446925,-15007440736⟩⟩⟩
noncomputable def centerBoxes119 := centerStep118.proposed :: centerBoxes118
theorem centerAccepted118 : StepValid centerStep118.shape centerBoxes118 centerStep118.proposed := by
  dsimp only [StepValid,centerStep118]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨175045458319,175045615483⟩,⟨1677948969101,1677954475107⟩,⟨106131671605,106134313504⟩,⟨-2092356175817,-2092146786194⟩,⟨476545225371,476675141478⟩,⟨-520784380242,-520690570255⟩⟩⟩
noncomputable def centerBoxes120 := centerStep119.proposed :: centerBoxes119
theorem centerAccepted119 : StepValid centerStep119.shape centerBoxes119 centerStep119.proposed := by
  dsimp only [StepValid,centerStep119]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-175045615483,-175045458319⟩,⟨-1677954475107,-1677948969101⟩,⟨-106134313504,-106131671605⟩,⟨2092146786194,2092356175817⟩,⟨-476675141478,-476545225371⟩,⟨520690570255,520784380242⟩⟩⟩
noncomputable def centerBoxes121 := centerStep120.proposed :: centerBoxes120
theorem centerAccepted120 : StepValid centerStep120.shape centerBoxes120 centerStep120.proposed := by
  dsimp only [StepValid,centerStep120]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨58310567370,58310785616⟩,⟨-92087282322,-92080113560⟩,⟨132320551904,132324038011⟩,⟨-1731056297494,-1730793016513⟩,⟨-1757036055092,-1756868134496⟩,⟨392449107175,392573793751⟩⟩⟩
noncomputable def centerBoxes122 := centerStep121.proposed :: centerBoxes121
theorem centerAccepted121 : StepValid centerStep121.shape centerBoxes121 centerStep121.proposed := by
  dsimp only [StepValid,centerStep121]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨27216840338704,27216865066304⟩,⟨-232585179679980,-232584574510019⟩,⟨-80510536299425,-80510127467087⟩,⟨3173816335051417,3173837463645287⟩,⟨1220771450993310,1220787973840377⟩,⟨283588675120503,283603319888518⟩⟩⟩
noncomputable def centerBoxes123 := centerStep122.proposed :: centerBoxes122
theorem centerAccepted122 : StepValid centerStep122.shape centerBoxes122 centerStep122.proposed := by
  dsimp only [StepValid,centerStep122]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨14395396719,14395396846⟩,⟨177383306802,177383309950⟩,⟨42325362732,42325364340⟩,⟨521154812525,521154900436⟩,⟨107276784568,107276825812⟩,⟨28082502389,28082517292⟩⟩⟩
noncomputable def centerBoxes124 := centerStep123.proposed :: centerBoxes123
theorem centerAccepted123 : StepValid centerStep123.shape centerBoxes123 centerStep123.proposed := by
  dsimp only [StepValid,centerStep123]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨356337490405,356337817297⟩,⟨1345740363821,1345752381106⟩,⟨-6383270884,-6376917245⟩,⟨-20591801743061,-20591314257908⟩,⟨-3303515247143,-3303205523517⟩,⟨-1790419534662,-1790195053026⟩⟩⟩
noncomputable def centerBoxes125 := centerStep124.proposed :: centerBoxes124
theorem centerAccepted124 : StepValid centerStep124.shape centerBoxes124 centerStep124.proposed := by
  dsimp only [StepValid,centerStep124]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-356337817297,-356337490405⟩,⟨-1345752381106,-1345740363821⟩,⟨6376917245,6383270884⟩,⟨20591314257908,20591801743061⟩,⟨3303205523517,3303515247143⟩,⟨1790195053026,1790419534662⟩⟩⟩
noncomputable def centerBoxes126 := centerStep125.proposed :: centerBoxes125
theorem centerAccepted125 : StepValid centerStep125.shape centerBoxes125 centerStep125.proposed := by
  dsimp only [StepValid,centerStep125]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨82421824352,82422316629⟩,⟨-533608374431,-533593019292⟩,⟨-80983420242,-80974197184⟩,⟨2514637087570,2515219556423⟩,⟨-2046499740384,-2046090799806⟩,⟨547421576252,547750415450⟩⟩⟩
noncomputable def centerBoxes127 := centerStep126.proposed :: centerBoxes126
theorem centerAccepted126 : StepValid centerStep126.shape centerBoxes126 centerStep126.proposed := by
  dsimp only [StepValid,centerStep126]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨243024525721,243024525726⟩,⟨1544972154842,1544972154851⟩,⟨304114937018,304114937023⟩,⟨-3890928397846,-3890928397841⟩,⟨-1531793878552,-1531793878544⟩,⟨-346708634503,-346708634500⟩⟩⟩
noncomputable def centerBoxes128 := centerStep127.proposed :: centerBoxes127
theorem centerAccepted127 : StepValid centerStep127.shape centerBoxes127 centerStep127.proposed := by
  dsimp only [StepValid,centerStep127]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1663691717297,-1663690231710⟩,⟨-4159207951684,-4159166350482⟩,⟨465212857178,465236555781⟩,⟨42319855142336,42321346742929⟩,⟨-7620884672508,-7619848028653⟩,⟨1793024197809,1793875723558⟩⟩⟩
noncomputable def centerBoxes129 := centerStep128.proposed :: centerBoxes128
theorem centerAccepted128 : StepValid centerStep128.shape centerBoxes128 centerStep128.proposed := by
  dsimp only [StepValid,centerStep128]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-190363973841,-190363803023⟩,⟨-1648761292272,-1648755467101⟩,⟨-226623324315,-226620353135⟩,⟨2758327924853,2758561099603⟩,⟨-228771483531,-228628038107⟩,⟨587404791826,587510476087⟩⟩⟩
noncomputable def centerBoxes130 := centerStep129.proposed :: centerBoxes129
theorem centerAccepted129 : StepValid centerStep129.shape centerBoxes129 centerStep129.proposed := by
  dsimp only [StepValid,centerStep129]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨52660551880,52660722703⟩,⟨-103789137430,-103783312250⟩,⟨77491612703,77494583888⟩,⟨-1132600472993,-1132367298238⟩,⟨-1760565362083,-1760421916651⟩,⟨240696157323,240801841587⟩⟩⟩
noncomputable def centerBoxes131 := centerStep130.proposed :: centerBoxes130
theorem centerAccepted130 : StepValid centerStep130.shape centerBoxes130 centerStep130.proposed := by
  dsimp only [StepValid,centerStep130]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨4371089145,4371131613⟩,⟨-35202147652,-35200648786⟩,⟨5624219220,5625044996⟩,⟨92967508565,93028939217⟩,⟨-297682246344,-297641938175⟩,⟨38957957915,38987761995⟩⟩⟩
noncomputable def centerBoxes132 := centerStep131.proposed :: centerBoxes131
theorem centerAccepted131 : StepValid centerStep131.shape centerBoxes131 centerStep131.proposed := by
  dsimp only [StepValid,centerStep131]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨2522150429,2522166793⟩,⟨-9941888468,-9941298228⟩,⟨7422842992,7423151680⟩,⟨-88898711584,-88873824655⟩,⟨-183273624046,-183257954468⟩,⟨33978981298,33990017144⟩⟩⟩
noncomputable def centerBoxes133 := centerStep132.proposed :: centerBoxes132
theorem centerAccepted132 : StepValid centerStep132.shape centerBoxes132 centerStep132.proposed := by
  dsimp only [StepValid,centerStep132]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨4341248088,4341276345⟩,⟨-34302919287,-34301791453⟩,⟨4994728753,4995310833⟩,⟨64112760334,64164175462⟩,⟨-278837584179,-278806314573⟩,⟨29404528229,29425538215⟩⟩⟩
noncomputable def centerBoxes134 := centerStep133.proposed :: centerBoxes133
theorem centerAccepted133 : StepValid centerStep133.shape centerBoxes133 centerStep133.proposed := by
  dsimp only [StepValid,centerStep133]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-4341276345,-4341248088⟩,⟨34301791453,34302919287⟩,⟨-4995310833,-4994728753⟩,⟨-64164175462,-64112760334⟩,⟨278806314573,278837584179⟩,⟨-29425538215,-29404528229⟩⟩⟩
noncomputable def centerBoxes135 := centerStep134.proposed :: centerBoxes134
theorem centerAccepted134 : StepValid centerStep134.shape centerBoxes134 centerStep134.proposed := by
  dsimp only [StepValid,centerStep134]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨29812800,29883525⟩,⟨-900356199,-897729499⟩,⟨628908387,630316243⟩,⟨28803333103,28916178883⟩,⟨-18875931771,-18804353996⟩,⟨9532419700,9583233766⟩⟩⟩
noncomputable def centerBoxes136 := centerStep135.proposed :: centerBoxes135
theorem centerAccepted135 : StepValid centerStep135.shape centerBoxes135 centerStep135.proposed := by
  dsimp only [StepValid,centerStep135]
  exact ⟨by decide,by decide⟩
noncomputable def centerProgram : List (Instruction 40) := [centerStep0,centerStep1,centerStep2,centerStep3,centerStep4,centerStep5,centerStep6,centerStep7,centerStep8,centerStep9,centerStep10,centerStep11,centerStep12,centerStep13,centerStep14,centerStep15,centerStep16,centerStep17,centerStep18,centerStep19,centerStep20,centerStep21,centerStep22,centerStep23,centerStep24,centerStep25,centerStep26,centerStep27,centerStep28,centerStep29,centerStep30,centerStep31,centerStep32,centerStep33,centerStep34,centerStep35,centerStep36,centerStep37,centerStep38,centerStep39,centerStep40,centerStep41,centerStep42,centerStep43,centerStep44,centerStep45,centerStep46,centerStep47,centerStep48,centerStep49,centerStep50,centerStep51,centerStep52,centerStep53,centerStep54,centerStep55,centerStep56,centerStep57,centerStep58,centerStep59,centerStep60,centerStep61,centerStep62,centerStep63,centerStep64,centerStep65,centerStep66,centerStep67,centerStep68,centerStep69,centerStep70,centerStep71,centerStep72,centerStep73,centerStep74,centerStep75,centerStep76,centerStep77,centerStep78,centerStep79,centerStep80,centerStep81,centerStep82,centerStep83,centerStep84,centerStep85,centerStep86,centerStep87,centerStep88,centerStep89,centerStep90,centerStep91,centerStep92,centerStep93,centerStep94,centerStep95,centerStep96,centerStep97,centerStep98,centerStep99,centerStep100,centerStep101,centerStep102,centerStep103,centerStep104,centerStep105,centerStep106,centerStep107,centerStep108,centerStep109,centerStep110,centerStep111,centerStep112,centerStep113,centerStep114,centerStep115,centerStep116,centerStep117,centerStep118,centerStep119,centerStep120,centerStep121,centerStep122,centerStep123,centerStep124,centerStep125,centerStep126,centerStep127,centerStep128,centerStep129,centerStep130,centerStep131,centerStep132,centerStep133,centerStep134,centerStep135]
theorem centerAccepted : Accepted centerProgram centerInitial :=
  ⟨centerAccepted0,⟨centerAccepted1,⟨centerAccepted2,⟨centerAccepted3,⟨centerAccepted4,⟨centerAccepted5,⟨centerAccepted6,⟨centerAccepted7,⟨centerAccepted8,⟨centerAccepted9,⟨centerAccepted10,⟨centerAccepted11,⟨centerAccepted12,⟨centerAccepted13,⟨centerAccepted14,⟨centerAccepted15,⟨centerAccepted16,⟨centerAccepted17,⟨centerAccepted18,⟨centerAccepted19,⟨centerAccepted20,⟨centerAccepted21,⟨centerAccepted22,⟨centerAccepted23,⟨centerAccepted24,⟨centerAccepted25,⟨centerAccepted26,⟨centerAccepted27,⟨centerAccepted28,⟨centerAccepted29,⟨centerAccepted30,⟨centerAccepted31,⟨centerAccepted32,⟨centerAccepted33,⟨centerAccepted34,⟨centerAccepted35,⟨centerAccepted36,⟨centerAccepted37,⟨centerAccepted38,⟨centerAccepted39,⟨centerAccepted40,⟨centerAccepted41,⟨centerAccepted42,⟨centerAccepted43,⟨centerAccepted44,⟨centerAccepted45,⟨centerAccepted46,⟨centerAccepted47,⟨centerAccepted48,⟨centerAccepted49,⟨centerAccepted50,⟨centerAccepted51,⟨centerAccepted52,⟨centerAccepted53,⟨centerAccepted54,⟨centerAccepted55,⟨centerAccepted56,⟨centerAccepted57,⟨centerAccepted58,⟨centerAccepted59,⟨centerAccepted60,⟨centerAccepted61,⟨centerAccepted62,⟨centerAccepted63,⟨centerAccepted64,⟨centerAccepted65,⟨centerAccepted66,⟨centerAccepted67,⟨centerAccepted68,⟨centerAccepted69,⟨centerAccepted70,⟨centerAccepted71,⟨centerAccepted72,⟨centerAccepted73,⟨centerAccepted74,⟨centerAccepted75,⟨centerAccepted76,⟨centerAccepted77,⟨centerAccepted78,⟨centerAccepted79,⟨centerAccepted80,⟨centerAccepted81,⟨centerAccepted82,⟨centerAccepted83,⟨centerAccepted84,⟨centerAccepted85,⟨centerAccepted86,⟨centerAccepted87,⟨centerAccepted88,⟨centerAccepted89,⟨centerAccepted90,⟨centerAccepted91,⟨centerAccepted92,⟨centerAccepted93,⟨centerAccepted94,⟨centerAccepted95,⟨centerAccepted96,⟨centerAccepted97,⟨centerAccepted98,⟨centerAccepted99,⟨centerAccepted100,⟨centerAccepted101,⟨centerAccepted102,⟨centerAccepted103,⟨centerAccepted104,⟨centerAccepted105,⟨centerAccepted106,⟨centerAccepted107,⟨centerAccepted108,⟨centerAccepted109,⟨centerAccepted110,⟨centerAccepted111,⟨centerAccepted112,⟨centerAccepted113,⟨centerAccepted114,⟨centerAccepted115,⟨centerAccepted116,⟨centerAccepted117,⟨centerAccepted118,⟨centerAccepted119,⟨centerAccepted120,⟨centerAccepted121,⟨centerAccepted122,⟨centerAccepted123,⟨centerAccepted124,⟨centerAccepted125,⟨centerAccepted126,⟨centerAccepted127,⟨centerAccepted128,⟨centerAccepted129,⟨centerAccepted130,⟨centerAccepted131,⟨centerAccepted132,⟨centerAccepted133,⟨centerAccepted134,⟨centerAccepted135,True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
noncomputable def center_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨58310567370,58310785616⟩,⟨-92087282322,-92080113560⟩,⟨132320551904,132324038011⟩,⟨-1731056297494,-1730793016513⟩,⟨-1757036055092,-1756868134496⟩,⟨392449107175,392573793751⟩⟩
theorem center_m11_eq : (finalBoxes centerProgram centerInitial).getD 14 (zeroBox 40)=center_m11 := rfl
noncomputable def center_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨29812800,29883525⟩,⟨-900356199,-897729499⟩,⟨628908387,630316243⟩,⟨28803333103,28916178883⟩,⟨-18875931771,-18804353996⟩,⟨9532419700,9583233766⟩⟩
theorem center_kdet_eq : (finalBoxes centerProgram centerInitial).getD 0 (zeroBox 40)=center_kdet := rfl
noncomputable def wholeInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨112957639884,113387136615⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨133143986176,137009456743⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def wholeBoxes0 := wholeInitial
noncomputable def wholeStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes1 := wholeStep0.proposed :: wholeBoxes0
theorem wholeAccepted0 : StepValid wholeStep0.shape wholeBoxes0 wholeStep0.proposed := by
  dsimp only [StepValid,wholeStep0]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes2 := wholeStep1.proposed :: wholeBoxes1
theorem wholeAccepted1 : StepValid wholeStep1.shape wholeBoxes1 wholeStep1.proposed := by
  dsimp only [StepValid,wholeStep1]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-113387136615,-112957639884⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes3 := wholeStep2.proposed :: wholeBoxes2
theorem wholeAccepted2 : StepValid wholeStep2.shape wholeBoxes2 wholeStep2.proposed := by
  dsimp only [StepValid,wholeStep2]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨436368677273,436798174004⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes4 := wholeStep3.proposed :: wholeBoxes3
theorem wholeAccepted3 : StepValid wholeStep3.shape wholeBoxes3 wholeStep3.proposed := by
  dsimp only [StepValid,wholeStep3]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨52841519513,54429147465⟩,⟨-137009456743,-133143986176⟩,⟨436368677273,436798174004⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes5 := wholeStep4.proposed :: wholeBoxes4
theorem wholeAccepted4 : StepValid wholeStep4.shape wholeBoxes4 wholeStep4.proposed := by
  dsimp only [StepValid,wholeStep4]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨165799159397,167816284080⟩,⟨962502171033,966367641600⟩,⟨436368677273,436798174004⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes6 := wholeStep5.proposed :: wholeBoxes5
theorem wholeAccepted5 : StepValid wholeStep5.shape wholeBoxes5 wholeStep5.proposed := by
  dsimp only [StepValid,wholeStep5]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨52412022782,54858644196⟩,⟨-137009456743,-133143986176⟩,⟨436368677273,436798174004⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes7 := wholeStep6.proposed :: wholeBoxes6
theorem wholeAccepted6 : StepValid wholeStep6.shape wholeBoxes6 wholeStep6.proposed := by
  dsimp only [StepValid,wholeStep6]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep7 : Instruction 40 := ⟨.log 7,⟨⟨-2502058066176,-2497885283648⟩,⟨10661930935953,10702470597440⟩,⟨0,0⟩,⟨-104176139656436,-103388421196570⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes8 := wholeStep7.proposed :: wholeBoxes7
theorem wholeAccepted7 : StepValid wholeStep7.shape wholeBoxes7 wholeStep7.proposed := by
  dsimp only [StepValid,wholeStep7]
  exact ⟨by decide,by decide,lc19,by decide⟩
noncomputable def wholeStep8 : Instruction 40 := ⟨.mul 8 0,⟨⟨-258024738076,-256618683435⟩,⟨-1406711255186,-1394193003281⟩,⟨0,0⟩,⟨10580697469779,10783396361089⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes9 := wholeStep8.proposed :: wholeBoxes8
theorem wholeAccepted8 : StepValid wholeStep8.shape wholeBoxes8 wholeStep8.proposed := by
  dsimp only [StepValid,wholeStep8]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep9 : Instruction 40 := ⟨.neg 0,⟨⟨256618683435,258024738076⟩,⟨1394193003281,1406711255186⟩,⟨0,0⟩,⟨-10783396361089,-10580697469779⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes10 := wholeStep9.proposed :: wholeBoxes9
theorem wholeAccepted9 : StepValid wholeStep9.shape wholeBoxes9 wholeStep9.proposed := by
  dsimp only [StepValid,wholeStep9]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep10 : Instruction 40 := ⟨.add 12 7,⟨⟨986124491161,986553987892⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes11 := wholeStep10.proposed :: wholeBoxes10
theorem wholeAccepted10 : StepValid wholeStep10.shape wholeBoxes10 wholeStep10.proposed := by
  dsimp only [StepValid,wholeStep10]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep11 : Instruction 40 := ⟨.log 0,⟨⟨-119669504256,-119190727040⟩,⟨-1225936309717,-1225402597781⟩,⟨0,0⟩,⟨-1366897627561,-1365707727607⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes12 := wholeStep11.proposed :: wholeBoxes11
theorem wholeAccepted11 : StepValid wholeStep11.shape wholeBoxes11 wholeStep11.proposed := by
  dsimp only [StepValid,wholeStep11]
  exact ⟨by decide,by decide,lc20,by decide⟩
noncomputable def wholeStep12 : Instruction 40 := ⟨.mul 1 0,⟨⟨-107375332530,-106899183313⟩,⟨-980799782110,-979363450628⟩,⟨0,0⟩,⟨1224334941456,1227003501238⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes13 := wholeStep12.proposed :: wholeBoxes12
theorem wholeAccepted12 : StepValid wholeStep12.shape wholeBoxes12 wholeStep12.proposed := by
  dsimp only [StepValid,wholeStep12]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep13 : Instruction 40 := ⟨.neg 0,⟨⟨106899183313,107375332530⟩,⟨979363450628,980799782110⟩,⟨0,0⟩,⟨-1227003501238,-1224334941456⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes14 := wholeStep13.proposed :: wholeBoxes13
theorem wholeAccepted13 : StepValid wholeStep13.shape wholeBoxes13 wholeStep13.proposed := by
  dsimp only [StepValid,wholeStep13]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep14 : Instruction 40 := ⟨.add 4 0,⟨⟨363517866748,365400070606⟩,⟨2373556453909,2387511037296⟩,⟨0,0⟩,⟨-12010399862327,-11805032411235⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes15 := wholeStep14.proposed :: wholeBoxes14
theorem wholeAccepted14 : StepValid wholeStep14.shape wholeBoxes14 wholeStep14.proposed := by
  dsimp only [StepValid,wholeStep14]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2080104746176,-2066808685888⟩,⟨6306195698540,6408551542181⟩,⟨2859033837444,2896665297071⟩,⟨-37352522548445,-36168880058805⟩,⟨-24174847724364,-23601714916552⟩,⟨-7631269766766,-7434277434777⟩⟩⟩
noncomputable def wholeBoxes16 := wholeStep15.proposed :: wholeBoxes15
theorem wholeAccepted15 : StepValid wholeStep15.shape wholeBoxes15 wholeStep15.proposed := by
  dsimp only [StepValid,wholeStep15]
  exact ⟨by decide,by decide,lc21,by decide⟩
noncomputable def wholeStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-317482271385,-311661226764⟩,⟨-877284011979,-831140406382⟩,⟨-395230515944,-378152404717⟩,⟨5339727582861,5811001546772⟩,⟨3382592349600,3612915029582⟩,⟨1104612504402,1180450704409⟩⟩⟩
noncomputable def wholeBoxes17 := wholeStep16.proposed :: wholeBoxes16
theorem wholeAccepted16 : StepValid wholeStep16.shape wholeBoxes16 wholeStep16.proposed := by
  dsimp only [StepValid,wholeStep16]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep17 : Instruction 40 := ⟨.neg 0,⟨⟨311661226764,317482271385⟩,⟨831140406382,877284011979⟩,⟨378152404717,395230515944⟩,⟨-5811001546772,-5339727582861⟩,⟨-3612915029582,-3382592349600⟩,⟨-1180450704409,-1104612504402⟩⟩⟩
noncomputable def wholeBoxes18 := wholeStep17.proposed :: wholeBoxes17
theorem wholeAccepted17 : StepValid wholeStep17.shape wholeBoxes17 wholeStep17.proposed := by
  dsimp only [StepValid,wholeStep17]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-167816284080,-165799159397⟩,⟨-966367641600,-962502171033⟩,⟨-436798174004,-436368677273⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes19 := wholeStep18.proposed :: wholeBoxes18
theorem wholeAccepted18 : StepValid wholeStep18.shape wholeBoxes18 wholeStep18.proposed := by
  dsimp only [StepValid,wholeStep18]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨931695343696,933712468379⟩,⟨-966367641600,-962502171033⟩,⟨-436798174004,-436368677273⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes20 := wholeStep19.proposed :: wholeBoxes19
theorem wholeAccepted19 : StepValid wholeStep19.shape wholeBoxes19 wholeStep19.proposed := by
  dsimp only [StepValid,wholeStep19]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep20 : Instruction 40 := ⟨.log 0,⟨⟨-182096177536,-179718302912⟩,⟨-1140429074628,-1133413512885⟩,⟨-515473941733,-513854586831⟩,⟨-1182869231577,-1168360714645⟩,⟨760094822180,767856292389⟩,⟨-241664915490,-240148925884⟩⟩⟩
noncomputable def wholeBoxes21 := wholeStep20.proposed :: wholeBoxes20
theorem wholeAccepted20 : StepValid wholeStep20.shape wholeBoxes20 wholeStep20.proposed := by
  dsimp only [StepValid,wholeStep20]
  exact ⟨by decide,by decide,lc22,by decide⟩
noncomputable def wholeStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-154637265414,-152288253957⟩,⟨-811136114459,-800377382626⟩,⟨-366418142583,-363085426256⟩,⟨979858835920,1014624352074⟩,⟨1361633851827,1378456822850⟩,⟨202648650855,206064684747⟩⟩⟩
noncomputable def wholeBoxes22 := wholeStep21.proposed :: wholeBoxes21
theorem wholeAccepted21 : StepValid wholeStep21.shape wholeBoxes21 wholeStep21.proposed := by
  dsimp only [StepValid,wholeStep21]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep22 : Instruction 40 := ⟨.neg 0,⟨⟨152288253957,154637265414⟩,⟨800377382626,811136114459⟩,⟨363085426256,366418142583⟩,⟨-1014624352074,-979858835920⟩,⟨-1378456822850,-1361633851827⟩,⟨-206064684747,-202648650855⟩⟩⟩
noncomputable def wholeBoxes23 := wholeStep22.proposed :: wholeBoxes22
theorem wholeAccepted22 : StepValid wholeStep22.shape wholeBoxes22 wholeStep22.proposed := by
  dsimp only [StepValid,wholeStep22]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨463949480721,472119536799⟩,⟨1631517789008,1688420126438⟩,⟨741237830973,761648658527⟩,⟨-6825625898846,-6319586418781⟩,⟨-4991371852432,-4744226201427⟩,⟨-1386515389156,-1307261155257⟩⟩⟩
noncomputable def wholeBoxes24 := wholeStep23.proposed :: wholeBoxes23
theorem wholeAccepted23 : StepValid wholeStep23.shape wholeBoxes23 wholeStep23.proposed := by
  dsimp only [StepValid,wholeStep23]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨827467347469,837519607405⟩,⟨4005074242917,4075931163734⟩,⟨741237830973,761648658527⟩,⟨-18836025761173,-18124618830016⟩,⟨-4991371852432,-4744226201427⟩,⟨-1386515389156,-1307261155257⟩⟩⟩
noncomputable def wholeBoxes25 := wholeStep24.proposed :: wholeBoxes24
theorem wholeAccepted24 : StepValid wholeStep24.shape wholeBoxes24 wholeStep24.proposed := by
  dsimp only [StepValid,wholeStep24]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨104824045564,109717288392⟩,⟨-274018913486,-266287972352⟩,⟨872737354546,873596348008⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes26 := wholeStep25.proposed :: wholeBoxes25
theorem wholeAccepted25 : StepValid wholeStep25.shape wholeBoxes25 wholeStep25.proposed := by
  dsimp only [StepValid,wholeStep25]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep26 : Instruction 40 := ⟨.inv 0,⟨⟨11018553569200,11532905576293⟩,⟨26742442610421,30147989789452⟩,⟨-96114437667068,-87646199006938⟩,⟨129809821639522,157618786060856⟩,⟨-281661708442764,-183501241134529⟩,⟨1394349294963143,1602022155985747⟩⟩⟩
noncomputable def wholeBoxes27 := wholeStep26.proposed :: wholeBoxes26
theorem wholeAccepted26 : StepValid wholeStep26.shape wholeBoxes26 wholeStep26.proposed := by
  dsimp only [StepValid,wholeStep26]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨8292311845117,8784840747918⟩,⟨60261866697956,65717232991417⟩,⟨-65784076789699,-57971506745988⟩,⟨94942350583200,161948266882067⟩,⟨-605173723090753,-484017758895356⟩,⟨901652216686498,1089017571918977⟩⟩⟩
noncomputable def wholeBoxes28 := wholeStep27.proposed :: wholeBoxes27
theorem wholeAccepted27 : StepValid wholeStep27.shape wholeBoxes27 wholeStep27.proposed := by
  dsimp only [StepValid,wholeStep27]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep28 : Instruction 40 := ⟨.contact 0,⟨⟨94874429440,100443949312⟩,⟨-786985527586,-643425568866⟩,⟨618971030105,787786004104⟩,⟨6725253907410,11262637026787⟩,⟨-7120903594056,-1088167922262⟩,⟨-5022820496703,2674253332672⟩⟩⟩
noncomputable def wholeBoxes29 := wholeStep28.proposed :: wholeBoxes28
theorem wholeAccepted28 : StepValid wholeStep28.shape wholeBoxes28 wholeStep28.proposed := by
  dsimp only [StepValid,wholeStep28]
  exact ⟨by decide,by decide,(⟨⟨94874429440,100443949312⟩,⟨-13167014177,-11739661138⟩,⟨2884462549,3436453209⟩⟩ : DyadicJetEnclosure 40),brwhole28_jet,by decide⟩
noncomputable def wholeStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes30 := wholeStep29.proposed :: wholeBoxes29
theorem wholeAccepted29 : StepValid wholeStep29.shape wholeBoxes29 wholeStep29.proposed := by
  dsimp only [StepValid,wholeStep29]
  exact ⟨by decide,by decide,lc4,by decide⟩
noncomputable def wholeStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1194386057216,1199955577088⟩,⟨-786985527586,-643425568866⟩,⟨618971030105,787786004104⟩,⟨6725253907410,11262637026787⟩,⟨-7120903594056,-1088167922262⟩,⟨-5022820496703,2674253332672⟩⟩⟩
noncomputable def wholeBoxes31 := wholeStep30.proposed :: wholeBoxes30
theorem wholeAccepted30 : StepValid wholeStep30.shape wholeBoxes30 wholeStep30.proposed := by
  dsimp only [StepValid,wholeStep30]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep31 : Instruction 40 := ⟨.log 0,⟨⟨91002385216,96117580928⟩,⟨-724472404249,-589566737372⟩,⟨567159199766,725209296005⟩,⟨5684949552387,10051874499402⟩,⟨-6251149116934,-519238143422⟩,⟨-5102168797919,2169270903498⟩⟩⟩
noncomputable def wholeBoxes32 := wholeStep31.proposed :: wholeBoxes31
theorem wholeAccepted31 : StepValid wholeStep31.shape wholeBoxes31 wholeStep31.proposed := by
  dsimp only [StepValid,wholeStep31]
  exact ⟨by decide,by decide,lc32,by decide⟩
noncomputable def wholeStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨98854780003,104898233341⟩,⟨-859452345197,-693693029816⟩,⟨667327986357,860326530803⟩,⟨7422134562930,12991803383731⟩,⟨-8482860461675,-1317899784054⟩,⟨-5368789999613,3640426209014⟩⟩⟩
noncomputable def wholeBoxes33 := wholeStep32.proposed :: wholeBoxes32
theorem wholeAccepted32 : StepValid wholeStep32.shape wholeBoxes32 wholeStep32.proposed := by
  dsimp only [StepValid,wholeStep32]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-100443949312,-94874429440⟩,⟨643425568866,786985527586⟩,⟨-787786004104,-618971030105⟩,⟨-11262637026787,-6725253907410⟩,⟨1088167922262,7120903594056⟩,⟨-2674253332672,5022820496703⟩⟩⟩
noncomputable def wholeBoxes34 := wholeStep33.proposed :: wholeBoxes33
theorem wholeAccepted33 : StepValid wholeStep33.shape wholeBoxes33 wholeStep33.proposed := by
  dsimp only [StepValid,wholeStep33]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨999067678464,1004637198336⟩,⟨643425568866,786985527586⟩,⟨-787786004104,-618971030105⟩,⟨-11262637026787,-6725253907410⟩,⟨1088167922262,7120903594056⟩,⟨-2674253332672,5022820496703⟩⟩⟩
noncomputable def wholeBoxes35 := wholeStep34.proposed :: wholeBoxes34
theorem wholeAccepted34 : StepValid wholeStep34.shape wholeBoxes34 wholeStep34.proposed := by
  dsimp only [StepValid,wholeStep34]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep35 : Instruction 40 := ⟨.log 0,⟨⟨-105331963712,-99219518912⟩,⟨704188433145,866107228895⟩,⟨-866988183467,-677424493124⟩,⟨-13077206385997,-7811364865966⟩,⟨1624791045020,8519766616813⟩,⟨-3626755093430,5110432524771⟩⟩⟩
noncomputable def wholeBoxes36 := wholeStep35.proposed :: wholeBoxes35
theorem wholeAccepted35 : StepValid wholeStep35.shape wholeBoxes35 wholeStep35.proposed := by
  dsimp only [StepValid,wholeStep35]
  exact ⟨by decide,by decide,lc33,by decide⟩
noncomputable def wholeStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-96243101252,-90155494415⟩,⟨564466219720,733310266239⟩,⟨-736321973639,-540070567587⟩,⟨-10517747652617,-4778975179498⟩,⟨-446922829345,6893571923635⟩,⟨-3032277481681,6168026886630⟩⟩⟩
noncomputable def wholeBoxes37 := wholeStep36.proposed :: wholeBoxes36
theorem wholeAccepted36 : StepValid wholeStep36.shape wholeBoxes36 wholeStep36.proposed := by
  dsimp only [StepValid,wholeStep36]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨2611678751,14742738926⟩,⟨-294986125477,39617236423⟩,⟨-68993987282,320255963216⟩,⟨-3095613089687,8212828204233⟩,⟨-8929783291020,5575672139581⟩,⟨-8401067481294,9808453095644⟩⟩⟩
noncomputable def wholeBoxes38 := wholeStep37.proposed :: wholeBoxes37
theorem wholeAccepted37 : StepValid wholeStep37.shape wholeBoxes37 wholeStep37.proposed := by
  dsimp only [StepValid,wholeStep37]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨1305839375,7371369463⟩,⟨-147493062739,19808618212⟩,⟨-34496993641,160127981608⟩,⟨-1547806544844,4106414102117⟩,⟨-4464891645510,2787836069791⟩,⟨-4200533740647,4904226547822⟩⟩⟩
noncomputable def wholeBoxes39 := wholeStep38.proposed :: wholeBoxes38
theorem wholeAccepted38 : StepValid wholeStep38.shape wholeBoxes38 wholeStep38.proposed := by
  dsimp only [StepValid,wholeStep38]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-7371369463,-1305839375⟩,⟨-19808618212,147493062739⟩,⟨-160127981608,34496993641⟩,⟨-4106414102117,1547806544844⟩,⟨-2787836069791,4464891645510⟩,⟨-4904226547822,4200533740647⟩⟩⟩
noncomputable def wholeBoxes40 := wholeStep39.proposed :: wholeBoxes39
theorem wholeAccepted39 : StepValid wholeStep39.shape wholeBoxes39 wholeStep39.proposed := by
  dsimp only [StepValid,wholeStep39]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨754752014153,760817563505⟩,⟨-19808618212,147493062739⟩,⟨-160127981608,34496993641⟩,⟨-4106414102117,1547806544844⟩,⟨-2787836069791,4464891645510⟩,⟨-4904226547822,4200533740647⟩⟩⟩
noncomputable def wholeBoxes41 := wholeStep40.proposed :: wholeBoxes40
theorem wholeAccepted40 : StepValid wholeStep40.shape wholeBoxes40 wholeStep40.proposed := by
  dsimp only [StepValid,wholeStep40]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨8186504930,9175880181⟩,⟨-143787355124,-111039541904⟩,⟨106819285648,143933607370⟩,⟨1913669784653,3184340972928⟩,⟨-2428765335432,-912225182974⟩,⟨-220801287044,1617480583186⟩⟩⟩
noncomputable def wholeBoxes42 := wholeStep41.proposed :: wholeBoxes41
theorem wholeAccepted41 : StepValid wholeStep41.shape wholeBoxes41 wholeStep41.proposed := by
  dsimp only [StepValid,wholeStep41]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-9175880181,-8186504930⟩,⟨111039541904,143787355124⟩,⟨-143933607370,-106819285648⟩,⟨-3184340972928,-1913669784653⟩,⟨912225182974,2428765335432⟩,⟨-1617480583186,220801287044⟩⟩⟩
noncomputable def wholeBoxes43 := wholeStep42.proposed :: wholeBoxes42
theorem wholeAccepted42 : StepValid wholeStep42.shape wholeBoxes42 wholeStep42.proposed := by
  dsimp only [StepValid,wholeStep42]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1090335747595,1091325122846⟩,⟨111039541904,143787355124⟩,⟨-143933607370,-106819285648⟩,⟨-3184340972928,-1913669784653⟩,⟨912225182974,2428765335432⟩,⟨-1617480583186,220801287044⟩⟩⟩
noncomputable def wholeBoxes44 := wholeStep43.proposed :: wholeBoxes43
theorem wholeAccepted43 : StepValid wholeStep43.shape wholeBoxes43 wholeStep43.proposed := by
  dsimp only [StepValid,wholeStep43]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep44 : Instruction 40 := ⟨.log 0,⟨⟨-9214382848,-8217133696⟩,⟨111872497856,144997418672⟩,⟨-145144901725,-107620583620⟩,⟨-3230260706062,-1939407795674⟩,⟨930018300584,2468345860359⟩,⟨-1650253091474,212125532159⟩⟩⟩
noncomputable def wholeBoxes45 := wholeStep44.proposed :: wholeBoxes44
theorem wholeAccepted44 : StepValid wholeStep44.shape wholeBoxes44 wholeStep44.proposed := by
  dsimp only [StepValid,wholeStep44]
  exact ⟨by decide,by decide,lc30,by decide⟩
noncomputable def wholeStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-4607191424,-4108566848⟩,⟨55936248928,72498709336⟩,⟨-72572450863,-53810291810⟩,⟨-1615130353031,-969703897837⟩,⟨465009150292,1234172930180⟩,⟨-825126545737,106062766080⟩⟩⟩
noncomputable def wholeBoxes46 := wholeStep45.proposed :: wholeBoxes45
theorem wholeAccepted45 : StepValid wholeStep45.shape wholeBoxes45 wholeStep45.proposed := by
  dsimp only [StepValid,wholeStep45]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep46 : Instruction 40 := ⟨.neg 0,⟨⟨4108566848,4607191424⟩,⟨-72498709336,-55936248928⟩,⟨53810291810,72572450863⟩,⟨969703897837,1615130353031⟩,⟨-1234172930180,-465009150292⟩,⟨-106062766080,825126545737⟩⟩⟩
noncomputable def wholeBoxes47 := wholeStep46.proposed :: wholeBoxes46
theorem wholeAccepted46 : StepValid wholeStep46.shape wholeBoxes46 wholeStep46.proposed := by
  dsimp only [StepValid,wholeStep46]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨766231950464,766730594304⟩,⟨-72498709336,-55936248928⟩,⟨53810291810,72572450863⟩,⟨969703897837,1615130353031⟩,⟨-1234172930180,-465009150292⟩,⟨-106062766080,825126545737⟩⟩⟩
noncomputable def wholeBoxes48 := wholeStep47.proposed :: wholeBoxes47
theorem wholeAccepted47 : StepValid wholeStep47.shape wholeBoxes47 wholeStep47.proposed := by
  dsimp only [StepValid,wholeStep47]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes49 := wholeStep48.proposed :: wholeBoxes48
theorem wholeAccepted48 : StepValid wholeStep48.shape wholeBoxes48 wholeStep48.proposed := by
  dsimp only [StepValid,wholeStep48]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes50 := wholeStep49.proposed :: wholeBoxes49
theorem wholeAccepted49 : StepValid wholeStep49.shape wholeBoxes49 wholeStep49.proposed := by
  dsimp only [StepValid,wholeStep49]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272583936898,272831280712⟩,⟨27759885476,35946838781⟩,⟨-35983401843,-26704821412⟩,⟨-796085243232,-478417446163⟩,⟨228056295743,607191333858⟩,⟨-404370145797,55200321761⟩⟩⟩
noncomputable def wholeBoxes51 := wholeStep50.proposed :: wholeBoxes50
theorem wholeAccepted50 : StepValid wholeStep50.shape wholeBoxes50 wholeStep50.proposed := by
  dsimp only [StepValid,wholeStep50]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1532463900928,1533461188608⟩,⟨-144997418672,-111872497856⟩,⟨107620583620,145144901726⟩,⟨1939407795674,3230260706062⟩,⟨-2468345860360,-930018300584⟩,⟨-212125532160,1650253091474⟩⟩⟩
noncomputable def wholeBoxes52 := wholeStep51.proposed :: wholeBoxes51
theorem wholeAccepted51 : StepValid wholeStep51.shape wholeBoxes51 wholeStep51.proposed := by
  dsimp only [StepValid,wholeStep51]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1203345667089,1210053978999⟩,⟨-953183642709,-770689530181⟩,⟨741398097107,954153166412⟩,⟨9042635354679,15142800170891⟩,⟨-10127929681149,-2253063237994⟩,⟨-5169984282243,4743750607448⟩⟩⟩
noncomputable def wholeBoxes53 := wholeStep52.proposed :: wholeBoxes52
theorem wholeAccepted52 : StepValid wholeStep52.shape wholeBoxes52 wholeStep52.proposed := by
  dsimp only [StepValid,wholeStep52]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1307179706402,1320596330222⟩,⟨-1906367285418,-1541379060362⟩,⟨1482796194214,1908306332825⟩,⟨18085270709364,30285600341781⟩,⟨-20255859362297,-4506126475988⟩,⟨-10335340914937,9487501214895⟩⟩⟩
noncomputable def wholeBoxes54 := wholeStep53.proposed :: wholeBoxes53
theorem wholeAccepted53 : StepValid wholeStep53.shape wholeBoxes53 wholeStep53.proposed := by
  dsimp only [StepValid,wholeStep53]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep54 : Instruction 40 := ⟨.log 0,⟨⟨190221904192,201449544576⟩,⟨-1603507908565,-1283332507361⟩,⟨1234557161676,1605138904793⟩,⟨12719038283192,23976324208525⟩,⟨-15596910661780,-1410837715832⟩,⟨-11036680097953,6594058325131⟩⟩⟩
noncomputable def wholeBoxes55 := wholeStep54.proposed :: wholeBoxes54
theorem wholeAccepted54 : StepValid wholeStep54.shape wholeBoxes54 wholeStep54.proposed := by
  dsimp only [StepValid,wholeStep54]
  exact ⟨by decide,by decide,lc35,by decide⟩
noncomputable def wholeStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨65125883985,69503149266⟩,⟨-546371727484,-428200981642⟩,⟨410260094945,548267455531⟩,⟨4030229930131,7963042712806⟩,⟨-5220939214449,-118792928626⟩,⟨-4153064856440,2283640788335⟩⟩⟩
noncomputable def wholeBoxes56 := wholeStep55.proposed :: wholeBoxes55
theorem wholeAccepted55 : StepValid wholeStep55.shape wholeBoxes55 wholeStep55.proposed := by
  dsimp only [StepValid,wholeStep55]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨379918713651,380510919068⟩,⟨2711377372,22399432263⟩,⟨-23504533408,-1204266816⟩,⟨-638955324385,129100557565⟩,⟨-289200080775,625760817946⟩,⟨-626101627561,481250243442⟩⟩⟩
noncomputable def wholeBoxes57 := wholeStep56.proposed :: wholeBoxes56
theorem wholeAccepted56 : StepValid wholeStep56.shape wholeBoxes56 wholeStep56.proposed := by
  dsimp only [StepValid,wholeStep56]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3177112032883,3182064415825⟩,⟨-187609701175,-22638902703⟩,⟨10055140076,196865636466⟩,⟨-1080977854953,5373785573750⟩,⟨-5264364498821,2422094019926⟩,⟨-4030717728003,5268364278181⟩⟩⟩
noncomputable def wholeBoxes58 := wholeStep57.proposed :: wholeBoxes57
theorem wholeAccepted57 : StepValid wholeStep57.shape wholeBoxes57 wholeStep57.proposed := by
  dsimp only [StepValid,wholeStep57]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨188185576608,201147029718⟩,⟨-1593097746905,-1238656177354⟩,⟨1186069434103,1599169211038⟩,⟨11594919343969,23571755402390⟩,⟨-15633920078846,-202516039259⟩,⟨-12266552427488,7138378389824⟩⟩⟩
noncomputable def wholeBoxes59 := wholeStep58.proposed :: wholeBoxes58
theorem wholeAccepted58 : StepValid wholeStep58.shape wholeBoxes58 wholeStep58.proposed := by
  dsimp only [StepValid,wholeStep58]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨378407480800,402596574294⟩,⟨-3196605655470,-2521988684715⟩,⟨2420626595779,3204308115831⟩,⟨24313957627161,47548079610915⟩,⟨-31230830740626,-1613353755091⟩,⟨-23303232525441,13732436714955⟩⟩⟩
noncomputable def wholeBoxes60 := wholeStep59.proposed :: wholeBoxes59
theorem wholeAccepted59 : StepValid wholeStep59.shape wholeBoxes59 wholeStep59.proposed := by
  dsimp only [StepValid,wholeStep59]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨518094205170,526454973568⟩,⟨-27413524812,204118464586⟩,⟨-221604169958,47741047912⟩,⟨-5688259272001,2181609684672⟩,⟨-3901100012642,6188303905762⟩,⟨-6797100699178,5859839468893⟩⟩⟩
noncomputable def wholeBoxes61 := wholeStep60.proposed :: wholeBoxes60
theorem wholeAccepted60 : StepValid wholeStep60.shape wholeBoxes60 wholeStep60.proposed := by
  dsimp only [StepValid,wholeStep60]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨355642118732,364285542933⟩,⟨-28453575153,211862579217⟩,⟨-230011680266,49552310546⟩,⟨-5909583976035,2305450410380⟩,⟨-4093695430611,6432690188180⟩,⟨-7065407231255,6130567929687⟩⟩⟩
noncomputable def wholeBoxes62 := wholeStep61.proposed :: wholeBoxes61
theorem wholeAccepted61 : StepValid wholeStep61.shape wholeBoxes61 wholeStep61.proposed := by
  dsimp only [StepValid,wholeStep61]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨711284237464,728571085866⟩,⟨-56907150306,423725158434⟩,⟨-460023360532,99104621092⟩,⟨-11819167952070,4610900820760⟩,⟨-8187390861222,12865380376360⟩,⟨-14130814462510,12261135859374⟩⟩⟩
noncomputable def wholeBoxes63 := wholeStep62.proposed :: wholeBoxes62
theorem wholeAccepted62 : StepValid wholeStep62.shape wholeBoxes62 wholeStep62.proposed := by
  dsimp only [StepValid,wholeStep62]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1523288020747,1525274683678⟩,⟨-33957876768,31914857268⟩,⟨-36313023750,38325616078⟩,⟨-1244933177254,1316590921409⟩,⟨-1556120677386,1498747034848⟩,⟨-1829606115346,1871054378518⟩⟩⟩
noncomputable def wholeBoxes64 := wholeStep63.proposed :: wholeBoxes63
theorem wholeAccepted63 : StepValid wholeStep63.shape wholeBoxes63 wholeStep63.proposed := by
  dsimp only [StepValid,wholeStep63]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨985429104071,1010695116321⟩,⟨-101444823334,608951722108⟩,⟨-662220013387,162876590649⟩,⟨-17247000496029,7293389557175⟩,⟨-12416269655018,18869326307051⟩,⟨-20847103797668,18279211797695⟩⟩⟩
noncomputable def wholeBoxes65 := wholeStep64.proposed :: wholeBoxes64
theorem wholeAccepted64 : StepValid wholeStep64.shape wholeBoxes64 wholeStep64.proposed := by
  dsimp only [StepValid,wholeStep64]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67577277745,67699973202⟩,⟨13764108862,17839596808⟩,⟨-17857742222,-13240979304⟩,⟨-393677228614,-234861974126⟩,⟨110723691946,299986761948⟩,⟨-199382479465,29749898550⟩⟩⟩
noncomputable def wholeBoxes66 := wholeStep65.proposed :: wholeBoxes65
theorem wholeAccepted65 : StepValid wholeStep65.shape wholeBoxes65 wholeStep65.proposed := by
  dsimp only [StepValid,wholeStep65]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50857116334,51568399593⟩,⟨256515127287,264555130956⟩,⟨31954755762,36931956629⟩,⟨-1359383787948,-1158448029210⟩,⟨-280924678750,-98953657277⟩,⟨-261985807294,-75537588033⟩⟩⟩
noncomputable def wholeBoxes67 := wholeStep66.proposed :: wholeBoxes66
theorem wholeAccepted66 : StepValid wholeStep66.shape wholeBoxes66 wholeStep66.proposed := by
  dsimp only [StepValid,wholeStep66]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2135898837557,2138679717034⟩,⟨-404448499434,-311848570110⟩,⟨299996207820,404859881240⟩,⟨5428933749180,9048569469550⟩,⟨-6923361457680,-2614359357462⟩,⟨-570624398575,4641453614847⟩⟩⟩
noncomputable def wholeBoxes68 := wholeStep67.proposed :: wholeBoxes67
theorem wholeAccepted67 : StepValid wholeStep67.shape wholeBoxes67 wholeStep67.proposed := by
  dsimp only [StepValid,wholeStep67]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2976947020752,2982762763109⟩,⟨-846111211113,-651966742565⟩,⟨627187581221,846971826886⟩,⟨11397604252540,19009722676468⟩,⟨-14563842879983,-5511500600476⟩,⟨-1149717179620,9790145201944⟩⟩⟩
noncomputable def wholeBoxes69 := wholeStep68.proposed :: wholeBoxes68
theorem wholeAccepted68 : StepValid wholeStep68.shape wholeBoxes68 wholeStep68.proposed := by
  dsimp only [StepValid,wholeStep68]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨137696534652,139895111770⟩,⟨654835587665,687530741683⟩,⟨115528170449,139913251238⟩,⟨-3567725964407,-2549146391202⟩,⟨-1327253976872,-338005991471⟩,⟨-728184507760,311548661332⟩⟩⟩
noncomputable def wholeBoxes70 := wholeStep69.proposed :: wholeBoxes69
theorem wholeAccepted69 : StepValid wholeStep69.shape wholeBoxes69 wholeStep69.proposed := by
  dsimp only [StepValid,wholeStep69]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8641658770766,8779638664619⟩,⟨-43837497421779,-40450775069668⟩,⟨-8920978246594,-7136453981840⟩,⟨536159315711532,665249850224866⟩,⟨87689557981266,173713187295573⟩,⟨-8077734376458,64558799705327⟩⟩⟩
noncomputable def wholeBoxes71 := wholeStep70.proposed :: wholeBoxes70
theorem wholeAccepted70 : StepValid wholeStep70.shape wholeBoxes70 wholeStep70.proposed := by
  dsimp only [StepValid,wholeStep70]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨7745022285383,8070435725489⟩,⟨-41106426078109,-31391205040176⟩,⟨-13488208042560,-5095418455989⟩,⟨294253116063828,677839374539477⟩,⟨-31987897968492,337578960218330⟩,⟨-176533105583690,216049956091678⟩⟩⟩
noncomputable def wholeBoxes72 := wholeStep71.proposed :: wholeBoxes71
theorem wholeAccepted71 : StepValid wholeStep71.shape wholeBoxes71 wholeStep71.proposed := by
  dsimp only [StepValid,wholeStep71]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨15490044570766,16140871450978⟩,⟨-82212852156218,-62782410080352⟩,⟨-26976416085120,-10190836911978⟩,⟨588506232127656,1355678749078954⟩,⟨-63975795936984,675157920436660⟩,⟨-353066211167380,432099912183356⟩⟩⟩
noncomputable def wholeBoxes73 := wholeStep72.proposed :: wholeBoxes72
theorem wholeAccepted72 : StepValid wholeStep72.shape wholeBoxes72 wholeStep72.proposed := by
  dsimp only [StepValid,wholeStep72]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10661930935953,10702470597440⟩,⟨-104176139656436,-103388421196570⟩,⟨0,0⟩,⟨2005108774710694,2028067813858452⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes74 := wholeStep73.proposed :: wholeBoxes73
theorem wholeAccepted73 : StepValid wholeStep73.shape wholeBoxes73 wholeStep73.proposed := by
  dsimp only [StepValid,wholeStep73]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9562419308177,9602958969664⟩,⟨-104176139656436,-103388421196570⟩,⟨0,0⟩,⟨2005108774710699,2028067813858436⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes75 := wholeStep74.proposed :: wholeBoxes74
theorem wholeAccepted74 : StepValid wholeStep74.shape wholeBoxes74 wholeStep74.proposed := by
  dsimp only [StepValid,wholeStep74]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep75 : Instruction 40 := ⟨.log 0,⟨⟨2378215779456,2382867339072⟩,⟨-11978441145317,-11837681660582⟩,⟨0,0⟩,⟨99082204851667,105744330752101⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes76 := wholeStep75.proposed :: wholeBoxes75
theorem wholeAccepted75 : StepValid wholeStep75.shape wholeBoxes75 wholeStep75.proposed := by
  dsimp only [StepValid,wholeStep75]
  exact ⟨by decide,by decide,lc36,by decide⟩
noncomputable def wholeStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7203864787271,7291507532436⟩,⟨-42498870099563,-41317417648639⟩,⟨-19209489285038,-18732037630962⟩,⟨473948096352001,495413040912289⟩,⟨262072224486325,272280964472712⟩,⟨97416940536641,101214865910915⟩⟩⟩
noncomputable def wholeBoxes77 := wholeStep76.proposed :: wholeBoxes76
theorem wholeAccepted76 : StepValid wholeStep76.shape wholeBoxes76 wholeStep76.proposed := by
  dsimp only [StepValid,wholeStep76]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6104353159495,6191995904660⟩,⟨-42498870099563,-41317417648638⟩,⟨-19209489285038,-18732037630961⟩,⟨473948096352002,495413040912281⟩,⟨262072224486326,272280964472708⟩,⟨97416940536640,101214865910914⟩⟩⟩
noncomputable def wholeBoxes78 := wholeStep77.proposed :: wholeBoxes77
theorem wholeAccepted77 : StepValid wholeStep77.shape wholeBoxes77 wholeStep77.proposed := by
  dsimp only [StepValid,wholeStep77]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep78 : Instruction 40 := ⟨.log 0,⟨⟨1884712508416,1900386443136⟩,⟨-7654865408509,-7336726611864⟩,⟨-3459999164653,-3326244639735⟩,⟨30865251737390,40277556455918⟩,⟨22447398814907,26847969123498⟩,⟨6410207546438,8168186116701⟩⟩⟩
noncomputable def wholeBoxes79 := wholeStep78.proposed :: wholeBoxes78
theorem wholeAccepted78 : StepValid wholeStep78.shape wholeBoxes78 wholeStep78.proposed := by
  dsimp only [StepValid,wholeStep78]
  exact ⟨by decide,by decide,lc37,by decide⟩
noncomputable def wholeStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨101308883270,101738380002⟩,⟨872737354546,873596348008⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes80 := wholeStep79.proposed :: wholeBoxes79
theorem wholeAccepted79 : StepValid wholeStep79.shape wholeBoxes79 wholeStep79.proposed := by
  dsimp only [StepValid,wholeStep79]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨140493561774,142510686458⟩,⟨668102588297,675506694394⟩,⟨303098948547,305130325937⟩,⟨-1698693120000,-1685130754127⟩,⟨-1535722599224,-1527865157872⟩,⟨-347049799190,-346367637584⟩⟩⟩
noncomputable def wholeBoxes81 := wholeStep80.proposed :: wholeBoxes80
theorem wholeAccepted80 : StepValid wholeStep80.shape wholeBoxes80 wholeStep80.proposed := by
  dsimp only [StepValid,wholeStep80]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4262928287872,4283253782208⟩,⟨-19633306553826,-19174408272446⟩,⟨-3459999164653,-3326244639735⟩,⟨129947456589057,146021887208019⟩,⟨22447398814907,26847969123498⟩,⟨6410207546438,8168186116701⟩⟩⟩
noncomputable def wholeBoxes82 := wholeStep81.proposed :: wholeBoxes81
theorem wholeAccepted81 : StepValid wholeStep81.shape wholeBoxes81 wholeStep81.proposed := by
  dsimp only [StepValid,wholeStep81]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨756814961600,805193148588⟩,⟨-6393211310940,-5043977369430⟩,⟨4841253191558,6408616231662⟩,⟨48627915254322,95096159221830⟩,⟨-62461661481252,-3226707510182⟩,⟨-46606465050882,27464873429910⟩⟩⟩
noncomputable def wholeBoxes83 := wholeStep82.proposed :: wholeBoxes82
theorem wholeAccepted82 : StepValid wholeStep82.shape wholeBoxes82 wholeStep82.proposed := by
  dsimp only [StepValid,wholeStep82]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5019743249472,5088446930796⟩,⟨-26026517864766,-24218385641876⟩,⟨1381254026905,3082371591927⟩,⟨178575371843379,241118046429849⟩,⟨-40014262666345,23621261613316⟩,⟨-40196257504444,35633059546611⟩⟩⟩
noncomputable def wholeBoxes84 := wholeStep83.proposed :: wholeBoxes83
theorem wholeAccepted83 : StepValid wholeStep83.shape wholeBoxes83 wholeStep83.proposed := by
  dsimp only [StepValid,wholeStep83]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨462518603768,470836628179⟩,⟨1576174035461,1811450649071⟩,⟨127268597660,285213438772⟩,⟨-35080741827674,-26175396071630⟩,⟨-2606170051197,4634728116847⟩,⟨-3719380511617,3297145442764⟩⟩⟩
noncomputable def wholeBoxes85 := wholeStep84.proposed :: wholeBoxes84
theorem wholeAccepted84 : StepValid wholeStep84.shape wholeBoxes84 wholeStep84.proposed := by
  dsimp only [StepValid,wholeStep84]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep85 : Instruction 40 := ⟨.mul 88 85,⟨⟨225915279768,226774273230⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes86 := wholeStep85.proposed :: wholeBoxes85
theorem wholeAccepted85 : StepValid wholeStep85.shape wholeBoxes85 wholeStep85.proposed := by
  dsimp only [StepValid,wholeStep85]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep86 : Instruction 40 := ⟨.neg 0,⟨⟨-226774273230,-225915279768⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes87 := wholeStep86.proposed :: wholeBoxes86
theorem wholeAccepted86 : StepValid wholeStep86.shape wholeBoxes86 wholeStep86.proposed := by
  dsimp only [StepValid,wholeStep86]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep87 : Instruction 40 := ⟨.add 89 0,⟨⟨872737354546,873596348008⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes88 := wholeStep87.proposed :: wholeBoxes87
theorem wholeAccepted87 : StepValid wholeStep87.shape wholeBoxes87 wholeStep87.proposed := by
  dsimp only [StepValid,wholeStep87]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep88 : Instruction 40 := ⟨.mul 12 0,⟨⟨1887708774940,1893262565501⟩,⟨-14282980494402,-14152591376986⟩,⟨0,0⟩,⟨125997226743230,131930939874303⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes89 := wholeStep88.proposed :: wholeBoxes88
theorem wholeAccepted88 : StepValid wholeStep88.shape wholeBoxes88 wholeStep88.proposed := by
  dsimp only [StepValid,wholeStep88]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep89 : Instruction 40 := ⟨.neg 91,⟨⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes90 := wholeStep89.proposed :: wholeBoxes89
theorem wholeAccepted89 : StepValid wholeStep89.shape wholeBoxes89 wholeStep89.proposed := by
  dsimp only [StepValid,wholeStep89]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep90 : Instruction 40 := ⟨.add 1 0,⟨⟨788197147164,793750937725⟩,⟨-14282980494402,-14152591376986⟩,⟨0,0⟩,⟨125997226743230,131930939874303⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes91 := wholeStep90.proposed :: wholeBoxes90
theorem wholeAccepted90 : StepValid wholeStep90.shape wholeBoxes90 wholeStep90.proposed := by
  dsimp only [StepValid,wholeStep90]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨37572141840,39603128492⟩,⟨-811538784337,-770077942197⟩,⟨312815742780,315329962371⟩,⟨9433674112950,10142102187662⟩,⟨-6467888110707,-6405006849897⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes92 := wholeStep91.proposed :: wholeBoxes91
theorem wholeAccepted91 : StepValid wholeStep91.shape wholeBoxes91 wholeStep91.proposed := by
  dsimp only [StepValid,wholeStep91]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨500090745608,510439756671⟩,⟨764635251124,1041372706874⟩,⟨440084340440,600543401143⟩,⟨-25647067714724,-16033293883968⟩,⟨-9074058161904,-1770278733050⟩,⟨-3719380511617,3297145442764⟩⟩⟩
noncomputable def wholeBoxes93 := wholeStep92.proposed :: wholeBoxes92
theorem wholeAccepted92 : StepValid wholeStep92.shape wholeBoxes92 wholeStep92.proposed := by
  dsimp only [StepValid,wholeStep92]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep93 : Instruction 40 := ⟨.inv 17,⟨⟨507340798957,508333108400⟩,⟨2520383226112,2560338836291⟩,⟨0,0⟩,⟨2439291441574,4695713285828⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes94 := wholeStep93.proposed :: wholeBoxes93
theorem wholeAccepted93 : StepValid wholeStep93.shape wholeBoxes93 wholeStep93.proposed := by
  dsimp only [StepValid,wholeStep93]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨230753756502,235989708162⟩,⟨1499166488410,1670071431072⟩,⟨203065374887,277646989919⟩,⟨-7242341648586,-368282974761⟩,⟨-3186381037744,581585451094⟩,⟨-1719567314279,1524356950329⟩⟩⟩
noncomputable def wholeBoxes95 := wholeStep94.proposed :: wholeBoxes94
theorem wholeAccepted94 : StepValid wholeStep94.shape wholeBoxes94 wholeStep94.proposed := by
  dsimp only [StepValid,wholeStep94]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-805193148588,-756814961600⟩,⟨5043977369430,6393211310940⟩,⟨-6408616231662,-4841253191558⟩,⟨-95096159221830,-48627915254322⟩,⟨3226707510182,62461661481252⟩,⟨-27464873429910,46606465050882⟩⟩⟩
noncomputable def wholeBoxes96 := wholeStep95.proposed :: wholeBoxes95
theorem wholeAccepted95 : StepValid wholeStep95.shape wholeBoxes95 wholeStep95.proposed := by
  dsimp only [StepValid,wholeStep95]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3457735139284,3526438820608⟩,⟨-14589329184396,-12781196961506⟩,⟨-9868615396315,-8167497831293⟩,⟨34851297367227,97393971953697⟩,⟨25674106325089,89309630604750⟩,⟨-21054665883472,54774651167583⟩⟩⟩
noncomputable def wholeBoxes97 := wholeStep96.proposed :: wholeBoxes96
theorem wholeAccepted96 : StepValid wholeStep96.shape wholeBoxes96 wholeStep96.proposed := by
  dsimp only [StepValid,wholeStep96]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨441822999518,457071307280⟩,⟨210080978987,533379666955⟩,⟨-325914942959,-64990157962⟩,⟨-18921431114592,-8208513068776⟩,⟨-11756626629414,-1715370745723⟩,⟨-9319403432160,1507219691991⟩⟩⟩
noncomputable def wholeBoxes98 := wholeStep97.proposed :: wholeBoxes97
theorem wholeAccepted97 : StepValid wholeStep97.shape wholeBoxes97 wholeStep97.proposed := by
  dsimp only [StepValid,wholeStep97]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨331598318794,335632568160⟩,⟨1925004342066,1932735283200⟩,⟨872737354546,873596348008⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes99 := wholeStep98.proposed :: wholeBoxes98
theorem wholeAccepted98 : StepValid wholeStep98.shape wholeBoxes98 wholeStep98.proposed := by
  dsimp only [StepValid,wholeStep98]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-335632568160,-331598318794⟩,⟨-1932735283200,-1925004342066⟩,⟨-873596348008,-872737354546⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes100 := wholeStep99.proposed :: wholeBoxes99
theorem wholeAccepted99 : StepValid wholeStep99.shape wholeBoxes99 wholeStep99.proposed := by
  dsimp only [StepValid,wholeStep99]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨763879059616,767913308982⟩,⟨-1932735283200,-1925004342066⟩,⟨-873596348008,-872737354546⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes101 := wholeStep100.proposed :: wholeBoxes100
theorem wholeAccepted100 : StepValid wholeStep100.shape wholeBoxes100 wholeStep100.proposed := by
  dsimp only [StepValid,wholeStep100]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1309392626876,1327254760230⟩,⟨-8686781216988,-8396865802912⟩,⟨-3926425110087,-3806878918229⟩,⟨47133453918602,55042008700293⟩,⟨31011673201757,34715805416271⟩,⟨9733866324883,11202922994890⟩⟩⟩
noncomputable def wholeBoxes102 := wholeStep101.proposed :: wholeBoxes101
theorem wholeAccepted101 : StepValid wholeStep101.shape wholeBoxes101 wholeStep101.proposed := by
  dsimp only [StepValid,wholeStep101]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1327254760230,-1309392626876⟩,⟨8396865802912,8686781216988⟩,⟨3806878918229,3926425110087⟩,⟨-55042008700293,-47133453918602⟩,⟨-34715805416271,-31011673201757⟩,⟨-11202922994890,-9733866324883⟩⟩⟩
noncomputable def wholeBoxes103 := wholeStep102.proposed :: wholeBoxes102
theorem wholeAccepted102 : StepValid wholeStep102.shape wholeBoxes102 wholeStep102.proposed := by
  dsimp only [StepValid,wholeStep102]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-227743132454,-209880999100⟩,⟨8396865802912,8686781216988⟩,⟨3806878918229,3926425110087⟩,⟨-55042008700293,-47133453918602⟩,⟨-34715805416271,-31011673201757⟩,⟨-11202922994890,-9733866324883⟩⟩⟩
noncomputable def wholeBoxes104 := wholeStep103.proposed :: wholeBoxes103
theorem wholeAccepted103 : StepValid wholeStep103.shape wholeBoxes103 wholeStep103.proposed := by
  dsimp only [StepValid,wholeStep103]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-11362935285,-10004703386⟩,⟨425680913942,461794118425⟩,⟨90993526275,112607143925⟩,⟨-4911155267012,-4280394959409⟩,⟨1321019621200,1739434846434⟩,⟨2462755464548,2655669062118⟩⟩⟩
noncomputable def wholeBoxes105 := wholeStep104.proposed :: wholeBoxes104
theorem wholeAccepted104 : StepValid wholeStep104.shape wholeBoxes104 wholeStep104.proposed := by
  dsimp only [StepValid,wholeStep104]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨430460064233,447066603894⟩,⟨635761892929,995173785380⟩,⟨-234921416684,47616985963⟩,⟨-23832586381604,-12488908028185⟩,⟨-10435607008214,24064100711⟩,⟨-6856647967612,4162888754109⟩⟩⟩
noncomputable def wholeBoxes106 := wholeStep105.proposed :: wholeBoxes105
theorem wholeAccepted105 : StepValid wholeStep105.shape wholeBoxes105 wholeStep105.proposed := by
  dsimp only [StepValid,wholeStep105]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-101738380002,-101308883270⟩,⟨-873596348008,-872737354546⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes107 := wholeStep106.proposed :: wholeBoxes106
theorem wholeAccepted106 : StepValid wholeStep106.shape wholeBoxes106 wholeStep106.proposed := by
  dsimp only [StepValid,wholeStep106]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4829238148,5076098742⟩,⟨28924487137,31319034564⟩,⟨40206963047,40417161119⟩,⟨-327433878249,-316190123618⟩,⟨244629257582,245740915920⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes108 := wholeStep107.proposed :: wholeBoxes107
theorem wholeAccepted107 : StepValid wholeStep107.shape wholeBoxes107 wholeStep107.proposed := by
  dsimp only [StepValid,wholeStep107]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨10445519698,11000947691⟩,⟨7262243973,15881706254⟩,⟨86966641867,87592282552⟩,⟨-956830586106,-818542884042⟩,⟨88809042402,99690417602⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes109 := wholeStep108.proposed :: wholeBoxes108
theorem wholeAccepted108 : StepValid wholeStep108.shape wholeBoxes108 wholeStep108.proposed := by
  dsimp only [StepValid,wholeStep108]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1443459721928,1460995196140⟩,⟨-7196556901287,-6902720010208⟩,⟨-1344784219775,-1277518692001⟩,⟨97256194092769,104154785691766⟩,⟨20395001739422,22061131685928⟩,⟨4514364987751,4923697024899⟩⟩⟩
noncomputable def wholeBoxes110 := wholeStep109.proposed :: wholeBoxes109
theorem wholeAccepted109 : StepValid wholeStep109.shape wholeBoxes109 wholeStep109.proposed := by
  dsimp only [StepValid,wholeStep109]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨13713076403,14617700554⟩,⟨-62469725309,-44473746394⟩,⟨100716482691,104253156102⟩,⟨-555356204283,-123682919552⟩,⟨-282390506430,-201219749721⟩,⟨-171376587148,-152829386673⟩⟩⟩
noncomputable def wholeBoxes111 := wholeStep110.proposed :: wholeBoxes110
theorem wholeAccepted110 : StepValid wholeStep110.shape wholeBoxes110 wholeStep110.proposed := by
  dsimp only [StepValid,wholeStep110]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-14617700554,-13713076403⟩,⟨44473746394,62469725309⟩,⟨-104253156102,-100716482691⟩,⟨123682919552,555356204283⟩,⟨201219749721,282390506430⟩,⟨152829386673,171376587148⟩⟩⟩
noncomputable def wholeBoxes112 := wholeStep111.proposed :: wholeBoxes111
theorem wholeAccepted111 : StepValid wholeStep111.shape wholeBoxes111 wholeStep111.proposed := by
  dsimp only [StepValid,wholeStep111]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-116356080556,-115021959673⟩,⟨-829122601614,-810267629237⟩,⟨-104253156102,-100716482691⟩,⟨2322706175104,2754379459835⟩,⟨201219749721,282390506430⟩,⟨152829386673,171376587148⟩⟩⟩
noncomputable def wholeBoxes113 := wholeStep112.proposed :: wholeBoxes112
theorem wholeAccepted112 : StepValid wholeStep112.shape wholeBoxes112 wholeStep112.proposed := by
  dsimp only [StepValid,wholeStep112]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨89841337220,94817208919⟩,⟨-618735113667,-577957342550⟩,⟨575363302454,596401258398⟩,⟨3248162402456,3917330141869⟩,⟨-3468581031272,-3025784475302⟩,⟨-2443512758319,-2232666094234⟩⟩⟩
noncomputable def wholeBoxes114 := wholeStep113.proposed :: wholeBoxes113
theorem wholeAccepted113 : StepValid wholeStep113.shape wholeBoxes113 wholeStep113.proposed := by
  dsimp only [StepValid,wholeStep113]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨117945411731,125990015242⟩,⟨-1442755517890,-1322776134780⟩,⟨639379383073,688092210002⟩,⟨19467891939147,22286614238032⟩,⟨-6174514309362,-4925213624288⟩,⟨-4336876205624,-3843512892880⟩⟩⟩
noncomputable def wholeBoxes115 := wholeStep114.proposed :: wholeBoxes114
theorem wholeAccepted114 : StepValid wholeStep114.shape wholeBoxes114 wholeStep114.proposed := by
  dsimp only [StepValid,wholeStep114]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-125990015242,-117945411731⟩,⟨1322776134780,1442755517890⟩,⟨-688092210002,-639379383073⟩,⟨-22286614238032,-19467891939147⟩,⟨4925213624288,6174514309362⟩,⟨3843512892880,4336876205624⟩⟩⟩
noncomputable def wholeBoxes116 := wholeStep115.proposed :: wholeBoxes115
theorem wholeAccepted115 : StepValid wholeStep115.shape wholeBoxes115 wholeStep115.proposed := by
  dsimp only [StepValid,wholeStep115]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨973521612534,981566216045⟩,⟨1322776134780,1442755517890⟩,⟨-688092210002,-639379383073⟩,⟨-22286614238032,-19467891939147⟩,⟨4925213624288,6174514309362⟩,⟨3843512892880,4336876205624⟩⟩⟩
noncomputable def wholeBoxes117 := wholeStep116.proposed :: wholeBoxes116
theorem wholeAccepted116 : StepValid wholeStep116.shape wholeBoxes116 wholeStep116.proposed := by
  dsimp only [StepValid,wholeStep116]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨124394790699,127223461507⟩,⟨760568436545,790044058864⟩,⟨179182174136,190700059265⟩,⟨-2797569462146,-2206836749275⟩,⟨-799747299102,-540620056895⟩,⟨-200615561655,-97075474865⟩⟩⟩
noncomputable def wholeBoxes118 := wholeStep117.proposed :: wholeBoxes117
theorem wholeAccepted117 : StepValid wholeStep117.shape wholeBoxes117 wholeStep117.proposed := by
  dsimp only [StepValid,wholeStep117]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨12032661476,12313410009⟩,⟨169527212300,175484194596⟩,⟨21072277760,22065230278⟩,⟨611261989759,764488636383⟩,⟨88674738690,115131039050⟩,⟨-17820453823,-12205446170⟩⟩⟩
noncomputable def wholeBoxes119 := wholeStep118.proposed :: wholeBoxes118
theorem wholeAccepted118 : StepValid wholeStep118.shape wholeBoxes118 wholeStep118.proposed := by
  dsimp only [StepValid,wholeStep118]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨169517500187,180761315350⟩,⟨1467618419951,1889046270216⟩,⟨-5239735510,212393528942⟩,⟨-11190732546910,7044843331365⟩,⟨-5422557220153,6476710987172⟩,⟨-5298323538929,4276509740845⟩⟩⟩
noncomputable def wholeBoxes120 := wholeStep119.proposed :: wholeBoxes119
theorem wholeAccepted119 : StepValid wholeStep119.shape wholeBoxes119 wholeStep119.proposed := by
  dsimp only [StepValid,wholeStep119]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-180761315350,-169517500187⟩,⟨-1889046270216,-1467618419951⟩,⟨-212393528942,5239735510⟩,⟨-7044843331365,11190732546910⟩,⟨-6476710987172,5422557220153⟩,⟨-4276509740845,5298323538929⟩⟩⟩
noncomputable def wholeBoxes121 := wholeStep120.proposed :: wholeBoxes120
theorem wholeAccepted120 : StepValid wholeStep120.shape wholeBoxes120 wholeStep120.proposed := by
  dsimp only [StepValid,wholeStep120]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨49992441152,66472207975⟩,⟨-389879781806,202453011121⟩,⟨-9328154055,282886725429⟩,⟨-14287184979951,10822449572149⟩,⟨-9663092024916,6004142671247⟩,⟨-5996077055124,6822680489258⟩⟩⟩
noncomputable def wholeBoxes122 := wholeStep121.proposed :: wholeBoxes121
theorem wholeAccepted121 : StepValid wholeStep121.shape wholeBoxes121 wholeStep121.proposed := by
  dsimp only [StepValid,wholeStep121]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨26552043671876,27897743426220⟩,⟨-254469694684761,-210978228831881⟩,⟨-97418721588579,-64328992741137⟩,⟨2281471042496195,4079161056618153⟩,⟨463596290703096,2007589329364890⟩,⟨-458270194325393,1036528566628963⟩⟩⟩
noncomputable def wholeBoxes123 := wholeStep122.proposed :: wholeBoxes122
theorem wholeAccepted122 : StepValid wholeStep122.shape wholeBoxes122 wholeStep122.proposed := by
  dsimp only [StepValid,wholeStep122]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨14073579180,14720907673⟩,⟨172095954396,182830517428⟩,⟨40544053350,44131450794⟩,⟨404812228021,636010771657⟩,⟨62816409472,151723961650⟩,⟨11974853517,44184760967⟩⟩⟩
noncomputable def wholeBoxes124 := wholeStep123.proposed :: wholeBoxes123
theorem wholeAccepted123 : StepValid wholeStep123.shape wholeBoxes123 wholeStep123.proposed := by
  dsimp only [StepValid,wholeStep123]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨339862061998,373511379860⟩,⟨748945618255,1938442489490⟩,⟨-325203046436,296339493041⟩,⟨-45649900655145,4706834558031⟩,⟨-18961935831964,12879919586373⟩,⟨-13666663492410,10254534779309⟩⟩⟩
noncomputable def wholeBoxes125 := wholeStep124.proposed :: wholeBoxes124
theorem wholeAccepted124 : StepValid wholeStep124.shape wholeBoxes124 wholeStep124.proposed := by
  dsimp only [StepValid,wholeStep124]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-373511379860,-339862061998⟩,⟨-1938442489490,-748945618255⟩,⟨-296339493041,325203046436⟩,⟨-4706834558031,45649900655145⟩,⟨-12879919586373,18961935831964⟩,⟨-10254534779309,13666663492410⟩⟩⟩
noncomputable def wholeBoxes126 := wholeStep125.proposed :: wholeBoxes125
theorem wholeAccepted125 : StepValid wholeStep125.shape wholeBoxes125 wholeStep125.proposed := by
  dsimp only [StepValid,wholeStep125]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨56948684373,107204541896⟩,⟨-1302680596561,246228167125⟩,⟨-531260909725,372820032399⟩,⟨-28539420939635,33160992626960⟩,⟨-23315526594587,18985999932675⟩,⟨-17111182746921,17829552246519⟩⟩⟩
noncomputable def wholeBoxes127 := wholeStep126.proposed :: wholeBoxes126
theorem wholeAccepted126 : StepValid wholeStep126.shape wholeBoxes126 wholeStep126.proposed := by
  dsimp only [StepValid,wholeStep126]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨241802445044,244249066460⟩,⟨1540839942843,1549103042402⟩,⟨303098948547,305130325937⟩,⟨-3897716375552,-3884154009679⟩,⟨-1535722599224,-1527865157872⟩,⟨-347049799190,-346367637584⟩⟩⟩
noncomputable def wholeBoxes128 := wholeStep127.proposed :: wholeBoxes127
theorem wholeAccepted127 : StepValid wholeStep127.shape wholeBoxes127 wholeStep127.proposed := by
  dsimp only [StepValid,wholeStep127]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1708111575494,-1620442419108⟩,⟨-5603765648009,-2714947588994⟩,⟨-464357761919,1435880437583⟩,⟨-18209479468671,102860224088597⟩,⟨-55353027804713,39053436307851⟩,⟨-41707014752371,44994813838864⟩⟩⟩
noncomputable def wholeBoxes129 := wholeStep128.proposed :: wholeBoxes128
theorem wholeAccepted128 : StepValid wholeStep128.shape wholeBoxes128 wholeStep128.proposed := by
  dsimp only [StepValid,wholeStep128]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-197643991919,-183331026678⟩,⟨-1875754483363,-1428072841284⟩,⟨-349986458358,-97931402831⟩,⟨-6907671053910,12491898501460⟩,⟨-6913671005870,6350555456435⟩,⟨-4843888449642,6016047972136⟩⟩⟩
noncomputable def wholeBoxes130 := wholeStep129.proposed :: wholeBoxes129
theorem wholeAccepted129 : StepValid wholeStep129.shape wholeBoxes129 wholeStep129.proposed := by
  dsimp only [StepValid,wholeStep129]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨44158453125,60918039782⟩,⟨-334914540520,121030201118⟩,⟨-46887509811,207198923106⟩,⟨-10805387429462,8607744491781⟩,⟨-8449393605094,4822690298563⟩,⟨-5190938248832,5669680334552⟩⟩⟩
noncomputable def wholeBoxes131 := wholeStep130.proposed :: wholeBoxes130
theorem wholeAccepted130 : StepValid wholeStep130.shape wholeBoxes130 wholeStep130.proposed := by
  dsimp only [StepValid,wholeStep130]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨2589334828,6481170754⟩,⟨-116769059735,34625565830⟩,⟨-33027487156,50121263976⟩,⟨-3598136266692,3983839451970⟩,⟨-2819095177802,1984967883038⟩,⟨-1892474856797,1934971549115⟩⟩⟩
noncomputable def wholeBoxes132 := wholeStep131.proposed :: wholeBoxes131
theorem wholeAccepted131 : StepValid wholeStep131.shape wholeBoxes131 wholeStep131.proposed := by
  dsimp only [StepValid,wholeStep131]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨1773486458,3375141724⟩,⟨-37111635362,13411268096⟩,⟨-5195570682,22959561176⟩,⟨-1271069405421,1157849821241⟩,⟨-1062497954804,580014178558⟩,⟨-592875629607,706344882762⟩⟩⟩
noncomputable def wholeBoxes133 := wholeStep132.proposed :: wholeBoxes132
theorem wholeAccepted132 : StepValid wholeStep132.shape wholeBoxes132 wholeStep132.proposed := by
  dsimp only [StepValid,wholeStep132]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨3039997055,5833565935⟩,⟨-87641369061,11345952575⟩,⟨-19601047493,34317953556⟩,⟨-2333860597750,2641603452851⟩,⟨-2002254294353,1237862674494⟩,⟨-1158882257800,1278613458991⟩⟩⟩
noncomputable def wholeBoxes134 := wholeStep133.proposed :: wholeBoxes133
theorem wholeAccepted133 : StepValid wholeStep133.shape wholeBoxes133 wholeStep133.proposed := by
  dsimp only [StepValid,wholeStep133]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-5833565935,-3039997055⟩,⟨-11345952575,87641369061⟩,⟨-34317953556,19601047493⟩,⟨-2641603452851,2333860597750⟩,⟨-1237862674494,2002254294353⟩,⟨-1278613458991,1158882257800⟩⟩⟩
noncomputable def wholeBoxes135 := wholeStep134.proposed :: wholeBoxes134
theorem wholeAccepted134 : StepValid wholeStep134.shape wholeBoxes134 wholeStep134.proposed := by
  dsimp only [StepValid,wholeStep134]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨-3244231107,3441173699⟩,⟨-128115012310,122266934891⟩,⟨-67345440712,69722311469⟩,⟨-6239739719543,6317700049720⟩,⟨-4056957852296,3987222177391⟩,⟨-3171088315788,3093853806915⟩⟩⟩
noncomputable def wholeBoxes136 := wholeStep135.proposed :: wholeBoxes135
theorem wholeAccepted135 : StepValid wholeStep135.shape wholeBoxes135 wholeStep135.proposed := by
  dsimp only [StepValid,wholeStep135]
  exact ⟨by decide,by decide⟩
noncomputable def wholeProgram : List (Instruction 40) := [wholeStep0,wholeStep1,wholeStep2,wholeStep3,wholeStep4,wholeStep5,wholeStep6,wholeStep7,wholeStep8,wholeStep9,wholeStep10,wholeStep11,wholeStep12,wholeStep13,wholeStep14,wholeStep15,wholeStep16,wholeStep17,wholeStep18,wholeStep19,wholeStep20,wholeStep21,wholeStep22,wholeStep23,wholeStep24,wholeStep25,wholeStep26,wholeStep27,wholeStep28,wholeStep29,wholeStep30,wholeStep31,wholeStep32,wholeStep33,wholeStep34,wholeStep35,wholeStep36,wholeStep37,wholeStep38,wholeStep39,wholeStep40,wholeStep41,wholeStep42,wholeStep43,wholeStep44,wholeStep45,wholeStep46,wholeStep47,wholeStep48,wholeStep49,wholeStep50,wholeStep51,wholeStep52,wholeStep53,wholeStep54,wholeStep55,wholeStep56,wholeStep57,wholeStep58,wholeStep59,wholeStep60,wholeStep61,wholeStep62,wholeStep63,wholeStep64,wholeStep65,wholeStep66,wholeStep67,wholeStep68,wholeStep69,wholeStep70,wholeStep71,wholeStep72,wholeStep73,wholeStep74,wholeStep75,wholeStep76,wholeStep77,wholeStep78,wholeStep79,wholeStep80,wholeStep81,wholeStep82,wholeStep83,wholeStep84,wholeStep85,wholeStep86,wholeStep87,wholeStep88,wholeStep89,wholeStep90,wholeStep91,wholeStep92,wholeStep93,wholeStep94,wholeStep95,wholeStep96,wholeStep97,wholeStep98,wholeStep99,wholeStep100,wholeStep101,wholeStep102,wholeStep103,wholeStep104,wholeStep105,wholeStep106,wholeStep107,wholeStep108,wholeStep109,wholeStep110,wholeStep111,wholeStep112,wholeStep113,wholeStep114,wholeStep115,wholeStep116,wholeStep117,wholeStep118,wholeStep119,wholeStep120,wholeStep121,wholeStep122,wholeStep123,wholeStep124,wholeStep125,wholeStep126,wholeStep127,wholeStep128,wholeStep129,wholeStep130,wholeStep131,wholeStep132,wholeStep133,wholeStep134,wholeStep135]
theorem wholeAccepted : Accepted wholeProgram wholeInitial :=
  ⟨wholeAccepted0,⟨wholeAccepted1,⟨wholeAccepted2,⟨wholeAccepted3,⟨wholeAccepted4,⟨wholeAccepted5,⟨wholeAccepted6,⟨wholeAccepted7,⟨wholeAccepted8,⟨wholeAccepted9,⟨wholeAccepted10,⟨wholeAccepted11,⟨wholeAccepted12,⟨wholeAccepted13,⟨wholeAccepted14,⟨wholeAccepted15,⟨wholeAccepted16,⟨wholeAccepted17,⟨wholeAccepted18,⟨wholeAccepted19,⟨wholeAccepted20,⟨wholeAccepted21,⟨wholeAccepted22,⟨wholeAccepted23,⟨wholeAccepted24,⟨wholeAccepted25,⟨wholeAccepted26,⟨wholeAccepted27,⟨wholeAccepted28,⟨wholeAccepted29,⟨wholeAccepted30,⟨wholeAccepted31,⟨wholeAccepted32,⟨wholeAccepted33,⟨wholeAccepted34,⟨wholeAccepted35,⟨wholeAccepted36,⟨wholeAccepted37,⟨wholeAccepted38,⟨wholeAccepted39,⟨wholeAccepted40,⟨wholeAccepted41,⟨wholeAccepted42,⟨wholeAccepted43,⟨wholeAccepted44,⟨wholeAccepted45,⟨wholeAccepted46,⟨wholeAccepted47,⟨wholeAccepted48,⟨wholeAccepted49,⟨wholeAccepted50,⟨wholeAccepted51,⟨wholeAccepted52,⟨wholeAccepted53,⟨wholeAccepted54,⟨wholeAccepted55,⟨wholeAccepted56,⟨wholeAccepted57,⟨wholeAccepted58,⟨wholeAccepted59,⟨wholeAccepted60,⟨wholeAccepted61,⟨wholeAccepted62,⟨wholeAccepted63,⟨wholeAccepted64,⟨wholeAccepted65,⟨wholeAccepted66,⟨wholeAccepted67,⟨wholeAccepted68,⟨wholeAccepted69,⟨wholeAccepted70,⟨wholeAccepted71,⟨wholeAccepted72,⟨wholeAccepted73,⟨wholeAccepted74,⟨wholeAccepted75,⟨wholeAccepted76,⟨wholeAccepted77,⟨wholeAccepted78,⟨wholeAccepted79,⟨wholeAccepted80,⟨wholeAccepted81,⟨wholeAccepted82,⟨wholeAccepted83,⟨wholeAccepted84,⟨wholeAccepted85,⟨wholeAccepted86,⟨wholeAccepted87,⟨wholeAccepted88,⟨wholeAccepted89,⟨wholeAccepted90,⟨wholeAccepted91,⟨wholeAccepted92,⟨wholeAccepted93,⟨wholeAccepted94,⟨wholeAccepted95,⟨wholeAccepted96,⟨wholeAccepted97,⟨wholeAccepted98,⟨wholeAccepted99,⟨wholeAccepted100,⟨wholeAccepted101,⟨wholeAccepted102,⟨wholeAccepted103,⟨wholeAccepted104,⟨wholeAccepted105,⟨wholeAccepted106,⟨wholeAccepted107,⟨wholeAccepted108,⟨wholeAccepted109,⟨wholeAccepted110,⟨wholeAccepted111,⟨wholeAccepted112,⟨wholeAccepted113,⟨wholeAccepted114,⟨wholeAccepted115,⟨wholeAccepted116,⟨wholeAccepted117,⟨wholeAccepted118,⟨wholeAccepted119,⟨wholeAccepted120,⟨wholeAccepted121,⟨wholeAccepted122,⟨wholeAccepted123,⟨wholeAccepted124,⟨wholeAccepted125,⟨wholeAccepted126,⟨wholeAccepted127,⟨wholeAccepted128,⟨wholeAccepted129,⟨wholeAccepted130,⟨wholeAccepted131,⟨wholeAccepted132,⟨wholeAccepted133,⟨wholeAccepted134,⟨wholeAccepted135,True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
noncomputable def whole_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨49992441152,66472207975⟩,⟨-389879781806,202453011121⟩,⟨-9328154055,282886725429⟩,⟨-14287184979951,10822449572149⟩,⟨-9663092024916,6004142671247⟩,⟨-5996077055124,6822680489258⟩⟩
theorem whole_m11_eq : (finalBoxes wholeProgram wholeInitial).getD 14 (zeroBox 40)=whole_m11 := rfl
noncomputable def whole_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨-3244231107,3441173699⟩,⟨-128115012310,122266934891⟩,⟨-67345440712,69722311469⟩,⟨-6239739719543,6317700049720⟩,⟨-4056957852296,3987222177391⟩,⟨-3171088315788,3093853806915⟩⟩
theorem whole_kdet_eq : (finalBoxes wholeProgram wholeInitial).getD 0 (zeroBox 40)=whole_kdet := rfl
theorem sameShape : shapes centerProgram=shapes wholeProgram := by decide
theorem kernelShape : shapes wholeProgram =
    shapes CorrectionFactorizedProgramKernel.kernelProgram := by decide
attribute [local irreducible] wholeProgram centerProgram
noncomputable def inputJets (u rho : ℝ) : List BivariateJet2 :=
  [BivariateJet2.affineA (527/5120) u, BivariateJet2.affineZ (629/5120) rho,
    BivariateJet2.const 1, BivariateJet2.const 2]
noncomputable def outputJet_m11 (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 14 zeroJet
theorem output_value_m11 (u rho t : ℝ) : (outputJet_m11 u rho).value t =
    Correction.Natural.m11 (527/5120+t*(u-(527/5120))) ((527/5120+t*(u-(527/5120)))+(629/5120+t*(rho-(629/5120)))*(1/2-(527/5120+t*(u-(527/5120))))) := by
  exact CorrectionFactorizedProgramKernel.output_value_m11_of_shapes wholeProgram kernelShape (527/5120) (629/5120) u rho t
theorem output_value_one_m11 (u rho : ℝ) : (outputJet_m11 u rho).value 1 =
    Correction.Natural.m11 u (u+rho*(1/2-u)) := by simp [output_value_m11]
noncomputable def outputJet_kdet (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 0 zeroJet
theorem output_value_kdet (u rho t : ℝ) : (outputJet_kdet u rho).value t =
    Correction.Natural.kdet (527/5120+t*(u-(527/5120))) ((527/5120+t*(u-(527/5120)))+(629/5120+t*(rho-(629/5120)))*(1/2-(527/5120+t*(u-(527/5120))))) := by
  exact CorrectionFactorizedProgramKernel.output_value_kdet_of_shapes wholeProgram kernelShape (527/5120) (629/5120) u rho t
theorem output_value_one_kdet (u rho : ℝ) : (outputJet_kdet u rho).value 1 =
    Correction.Natural.kdet u (u+rho*(1/2-u)) := by simp [output_value_kdet]

private theorem center_A (x : ℝ) :
    (⟨⟨113172388249,113172388250⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩ : DyadicBivariateJetEnclosure 40).Contains (BivariateJet2.affineA (527/5120) x) 0 := by
  apply DyadicBivariateJetEnclosure.contains_coordinateA
  norm_num [DyadicInterval.Contains,DyadicInterval.scale]
private theorem whole_A {x t : ℝ} (hx : x∈Icc (263/2560:ℝ) (33/320)) (ht : t∈Icc (0:ℝ) 1) :
    (⟨⟨112957639884,113387136615⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩ : DyadicBivariateJetEnclosure 40).Contains (BivariateJet2.affineA (527/5120) x) t := by
  apply DyadicBivariateJetEnclosure.contains_coordinateA
  change (⟨112957639884,113387136615⟩ : DyadicInterval 40).Contains ((Jet2.segment (527/5120) x).value t)
  apply DyadicInterval.contains_segment _ _ ht
  · norm_num [DyadicInterval.Contains,DyadicInterval.scale]
  · norm_num [DyadicInterval.Contains,DyadicInterval.scale]
    constructor <;> linarith [hx.1,hx.2]
private theorem center_Z (x : ℝ) :
    (⟨⟨135076721459,135076721460⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩ : DyadicBivariateJetEnclosure 40).Contains (BivariateJet2.affineZ (629/5120) x) 0 := by
  apply DyadicBivariateJetEnclosure.contains_coordinateZ
  norm_num [DyadicInterval.Contains,DyadicInterval.scale]
private theorem whole_Z {x t : ℝ} (hx : x∈Icc (31/256:ℝ) (319/2560)) (ht : t∈Icc (0:ℝ) 1) :
    (⟨⟨133143986176,137009456743⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩ : DyadicBivariateJetEnclosure 40).Contains (BivariateJet2.affineZ (629/5120) x) t := by
  apply DyadicBivariateJetEnclosure.contains_coordinateZ
  change (⟨133143986176,137009456743⟩ : DyadicInterval 40).Contains ((Jet2.segment (629/5120) x).value t)
  apply DyadicInterval.contains_segment _ _ ht
  · norm_num [DyadicInterval.Contains,DyadicInterval.scale]
  · norm_num [DyadicInterval.Contains,DyadicInterval.scale]
    constructor <;> linarith [hx.1,hx.2]
theorem initial_center (a z : ℝ) : RegistersContain centerInitial (inputJets a z) 0 := by
  simpa [centerInitial,inputJets,DyadicBivariateJetEnclosure.const,DyadicInterval.ofInt,DyadicInterval.scale] using
    ((((RegistersContain.nil 40 0).cons (DyadicBivariateJetEnclosure.contains_const 40 2 0)).cons
      (DyadicBivariateJetEnclosure.contains_const 40 1 0)).cons (center_Z z)).cons (center_A a)

theorem initial_whole {a z : ℝ} (ha : a ∈ Icc (263/2560:ℝ) (33/320))
    (hz : z ∈ Icc (31/256:ℝ) (319/2560)) :
    ∀ t ∈ Icc (0:ℝ) 1, RegistersContain wholeInitial (inputJets a z) t := by
  intro t ht
  simpa [wholeInitial,inputJets,DyadicBivariateJetEnclosure.const,DyadicInterval.ofInt,DyadicInterval.scale] using
    ((((RegistersContain.nil 40 t).cons (DyadicBivariateJetEnclosure.contains_const 40 2 t)).cons
      (DyadicBivariateJetEnclosure.contains_const 40 1 t)).cons (whole_Z hz ht)).cons (whole_A ha ht)

theorem initial_sound (a z : ℝ) : ∀ i, ((inputJets a z).getD i zeroJet).DirectionalSoundOn
    (a-527/5120) (z-629/5120) (Icc (0:ℝ) 1) := by
  intro i t ht
  have hconst (c : ℝ) : (BivariateJet2.const c).DirectionalSoundAt (a-527/5120) (z-629/5120) t := by
    simpa only [BivariateJet2.DirectionalSoundAt,BivariateJet2.projection_const] using Jet2.soundAt_const c t
  have h : RegistersSound (inputJets a z) (a-527/5120) (z-629/5120) t :=
    ((((RegistersSound.nil _ _ t).cons (hconst 2)).cons (hconst 1)).cons
      (BivariateJet2.soundOn_affineZ (629/5120) z (a-527/5120) _ t ht)).cons
      (BivariateJet2.soundOn_affineA (527/5120) a (z-629/5120) _ t ht)
  exact h i

theorem taylor_positive_m11 : 0 < BivariateJetEnclosure.taylorLower
    center_m11.toReal whole_m11.toReal (1/5120) (9/5120) := by
  norm_num [BivariateJetEnclosure.taylorLower,JetBounds.Interval.magnitude,
    DyadicBivariateJetEnclosure.toReal,DyadicInterval.toReal,DyadicInterval.scale,center_m11,whole_m11]
theorem positive_m11 {a z : ℝ} (ha : a∈Icc (263/2560:ℝ) (33/320))
    (hz : z∈Icc (31/256:ℝ) (319/2560)) : 0 < Correction.Natural.m11 a (a+z*(1/2-a)) := by
  have hp := value_pos_of_accepted_taylor centerProgram wholeProgram 14 sameShape
    (initial_center a z) (initial_whole ha hz) (initial_sound a z) centerAccepted wholeAccepted
    (show (0:ℝ)≤1/5120 by norm_num) (show (0:ℝ)≤9/5120 by norm_num)
    (by rw [abs_le]; constructor <;> linarith [ha.1,ha.2])
    (by rw [abs_le]; constructor <;> linarith [hz.1,hz.2])
    (by rw [center_m11_eq,whole_m11_eq]; exact taylor_positive_m11)
  change 0 < (outputJet_m11 a z).value 1 at hp
  simpa only [output_value_one_m11] using hp
theorem taylor_positive_kdet : 0 < BivariateJetEnclosure.taylorLower
    center_kdet.toReal whole_kdet.toReal (1/5120) (9/5120) := by
  norm_num [BivariateJetEnclosure.taylorLower,JetBounds.Interval.magnitude,
    DyadicBivariateJetEnclosure.toReal,DyadicInterval.toReal,DyadicInterval.scale,center_kdet,whole_kdet]
theorem positive_kdet {a z : ℝ} (ha : a∈Icc (263/2560:ℝ) (33/320))
    (hz : z∈Icc (31/256:ℝ) (319/2560)) : 0 < Correction.Natural.kdet a (a+z*(1/2-a)) := by
  have hp := value_pos_of_accepted_taylor centerProgram wholeProgram 0 sameShape
    (initial_center a z) (initial_whole ha hz) (initial_sound a z) centerAccepted wholeAccepted
    (show (0:ℝ)≤1/5120 by norm_num) (show (0:ℝ)≤9/5120 by norm_num)
    (by rw [abs_le]; constructor <;> linarith [ha.1,ha.2])
    (by rw [abs_le]; constructor <;> linarith [hz.1,hz.2])
    (by rw [center_kdet_eq,whole_kdet_eq]; exact taylor_positive_kdet)
  change 0 < (outputJet_kdet a z).value 1 at hp
  simpa only [output_value_one_kdet] using hp

theorem _root_.solution {u rho : ℝ} (hu : u∈Icc (263/2560:ℝ) (33/320))
    (hr : rho∈Icc (31/256:ℝ) (319/2560)) (hr1 : rho < 1) :
    0 < Correction.Mleft (H u) (H (u+rho*(1/2-u))) ∧
    0 < Correction.Mdet (H u) (H (u+rho*(1/2-u))) := by
  let w := u+rho*(1/2-u)
  have hu0 : 0<u := by linarith [hu.1]
  have hgap : 0<1/2-u := by linarith [hu.2]
  have huw : u<w := by dsimp [w]; nlinarith [mul_pos (show 0<rho by linarith [hr.1]) hgap]
  have hw : w<1/2 := by dsimp [w]; nlinarith [mul_pos (show 0<1-rho by linarith [hr1]) hgap]
  have heq := Correction.Natural.kernel_eq_actual_ratio hu0 hgap (show 0<rho by linarith [hr.1]) hr1
  have hm := positive_m11 hu hr
  have hk := positive_kdet hu hr
  rw [heq.1] at hm
  rw [heq.2] at hk
  have hf0 := H_pos (hu0.trans huw) (show w<1 by linarith)
  have hf1 : H w<1 := by
    have h := H_strictMonoOn ⟨(hu0.trans huw).le,hw.le⟩
      (by norm_num : (1/2:ℝ)∈Icc 0 (1/2)) hw
    simpa only [H_half] using h
  exact ⟨hm,(Correction.Mdet_pos_iff_Kfactored_pos hf0 hf1).mpr hk⟩




end GeneralCK.Certificates.LaneCB.RB2Cell000062
end

