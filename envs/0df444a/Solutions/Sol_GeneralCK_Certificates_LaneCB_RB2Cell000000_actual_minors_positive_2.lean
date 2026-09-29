-- Prove2me | solution 2 for GeneralCK.Certificates.LaneCB.RB2Cell000000.actual_minors_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-25T05:09:24.050318+00:00
-- url     : https://prove2.me/submissions/2fe5e6f3-d2fa-48e8-8a89-4e77d7bfc5e2

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

namespace LaneCBRB2Cell000000Endpoints
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
noncomputable def out_w0 : DyadicInterval 40 := ⟨-2529573748800,-2529573690944⟩
theorem checked_w0 : DyadicFastLog.check 110165911142 1099511627776 3 16 (lift40 out_w0)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w0 : out_w0.Contains (Real.log ((110165911142:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w0

noncomputable def out_w1 : DyadicInterval 40 := ⟨-2529573748800,-2529573690944⟩
theorem checked_w1 : DyadicFastLog.check 110165911143 1099511627776 3 16 (lift40 out_w1)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w1 : out_w1.Contains (Real.log ((110165911143:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w1

noncomputable def out_w2 : DyadicInterval 40 := ⟨-116083747264,-116083747200⟩
theorem checked_w2 : DyadicFastLog.check 989345716633 1099511627776 0 16 (lift40 out_w2)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w2 : out_w2.Contains (Real.log ((989345716633:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w2

noncomputable def out_w3 : DyadicInterval 40 := ⟨-116083747264,-116083747200⟩
theorem checked_w3 : DyadicFastLog.check 989345716634 1099511627776 0 16 (lift40 out_w3)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w3 : out_w3.Contains (Real.log ((989345716634:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w3

noncomputable def out_w4 : DyadicInterval 40 := ⟨-2154885614464,-2154885574912⟩
theorem checked_w4 : DyadicFastLog.check 154897618042 1099511627776 2 16 (lift40 out_w4)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w4 : out_w4.Contains (Real.log ((154897618042:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w4

noncomputable def out_w5 : DyadicInterval 40 := ⟨-2154885614400,-2154885574912⟩
theorem checked_w5 : DyadicFastLog.check 154897618044 1099511627776 2 16 (lift40 out_w5)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w5 : out_w5.Contains (Real.log ((154897618044:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w5

noncomputable def out_w6 : DyadicInterval 40 := ⟨-166955339520,-166955339456⟩
theorem checked_w6 : DyadicFastLog.check 944614009732 1099511627776 0 16 (lift40 out_w6)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w6 : out_w6.Contains (Real.log ((944614009732:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w6

noncomputable def out_w7 : DyadicInterval 40 := ⟨-166955339520,-166955339456⟩
theorem checked_w7 : DyadicFastLog.check 944614009734 1099511627776 0 16 (lift40 out_w7)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w7 : out_w7.Contains (Real.log ((944614009734:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w7

noncomputable def out_w8 : DyadicInterval 40 := ⟨762123383616,762123402880⟩
theorem checked_w8 : DyadicFastLog.check 1099511627776 2199023255552 1 16 (lift40 out_w8.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w8 : out_w8.Contains (Real.log ((2199023255552:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w8

noncomputable def out_w9 : DyadicInterval 40 := ⟨81268356672,81268356736⟩
theorem checked_w9 : DyadicFastLog.check 1099511627776 1183858768896 0 16 (lift40 out_w9.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w9 : out_w9.Contains (Real.log ((1183858768896:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w9

noncomputable def out_w10 : DyadicInterval 40 := ⟨-87758016768,-87758016704⟩
theorem checked_w10 : DyadicFastLog.check 1015164486656 1099511627776 0 16 (lift40 out_w10)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w10 : out_w10.Contains (Real.log ((1015164486656:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w10

noncomputable def out_w11 : DyadicInterval 40 := ⟨81268480576,81268480640⟩
theorem checked_w11 : DyadicFastLog.check 1099511627776 1183858902272 0 16 (lift40 out_w11.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w11 : out_w11.Contains (Real.log ((1183858902272:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w11

noncomputable def out_w12 : DyadicInterval 40 := ⟨-87758161280,-87758161216⟩
theorem checked_w12 : DyadicFastLog.check 1015164353280 1099511627776 0 16 (lift40 out_w12)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w12 : out_w12.Contains (Real.log ((1015164353280:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w12

noncomputable def out_w13 : DyadicInterval 40 := ⟨-6489680640,-6489680576⟩
theorem checked_w13 : DyadicFastLog.check 1093041061630 1099511627776 0 16 (lift40 out_w13)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w13 : out_w13.Contains (Real.log ((1093041061630:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w13

noncomputable def out_w14 : DyadicInterval 40 := ⟨-6489660096,-6489660032⟩
theorem checked_w14 : DyadicFastLog.check 1093041082095 1099511627776 0 16 (lift40 out_w14)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w14 : out_w14.Contains (Real.log ((1093041082095:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w14

noncomputable def out_w15 : DyadicInterval 40 := ⟨169026373440,169026373504⟩
theorem checked_w15 : DyadicFastLog.check 1099511627776 1282222239996 0 16 (lift40 out_w15.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w15 : out_w15.Contains (Real.log ((1282222239996:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w15

noncomputable def out_w16 : DyadicInterval 40 := ⟨169026641792,169026641856⟩
theorem checked_w16 : DyadicFastLog.check 1099511627776 1282222552920 0 16 (lift40 out_w16.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w16 : out_w16.Contains (Real.log ((1282222552920:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w16

noncomputable def out_w17 : DyadicInterval 40 := ⟨2413489943680,2413490001536⟩
theorem checked_w17 : DyadicFastLog.check 1099511627776 9874171674723 3 16 (lift40 out_w17.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w17 : out_w17.Contains (Real.log ((9874171674723:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w17

noncomputable def out_w18 : DyadicInterval 40 := ⟨2413489943680,2413490001536⟩
theorem checked_w18 : DyadicFastLog.check 1099511627776 9874171674824 3 16 (lift40 out_w18.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w18 : out_w18.Contains (Real.log ((9874171674824:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w18

noncomputable def out_w19 : DyadicInterval 40 := ⟨1987930235456,1987930274048⟩
theorem checked_w19 : DyadicFastLog.check 1099511627776 6705165002378 2 16 (lift40 out_w19.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w19 : out_w19.Contains (Real.log ((6705165002378:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w19

noncomputable def out_w20 : DyadicInterval 40 := ⟨1987930235520,1987930274112⟩
theorem checked_w20 : DyadicFastLog.check 1099511627776 6705165002480 2 16 (lift40 out_w20.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w20 : out_w20.Contains (Real.log ((6705165002480:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w20

noncomputable def out_w21 : DyadicInterval 40 := ⟨-2531719137984,-2531719080128⟩
theorem checked_w21 : DyadicFastLog.check 109951162777 1099511627776 3 16 (lift40 out_w21)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w21 : out_w21.Contains (Real.log ((109951162777:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w21

noncomputable def out_w22 : DyadicInterval 40 := ⟨-2527432537536,-2527432479680⟩
theorem checked_w22 : DyadicFastLog.check 110380659508 1099511627776 3 16 (lift40 out_w22)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w22 : out_w22.Contains (Real.log ((110380659508:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w22

noncomputable def out_w23 : DyadicInterval 40 := ⟨-116322434304,-116322434240⟩
theorem checked_w23 : DyadicFastLog.check 989130968268 1099511627776 0 16 (lift40 out_w23)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w23 : out_w23.Contains (Real.log ((989130968268:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w23

noncomputable def out_w24 : DyadicInterval 40 := ⟨-115845112128,-115845112064⟩
theorem checked_w24 : DyadicFastLog.check 989560464999 1099511627776 0 16 (lift40 out_w24)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w24 : out_w24.Contains (Real.log ((989560464999:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w24

noncomputable def out_w25 : DyadicInterval 40 := ⟨-2162070810560,-2162070770880⟩
theorem checked_w25 : DyadicFastLog.check 153888678214 1099511627776 2 16 (lift40 out_w25)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w25 : out_w25.Contains (Real.log ((153888678214:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w25

noncomputable def out_w26 : DyadicInterval 40 := ⟨-2147741743808,-2147741704512⟩
theorem checked_w26 : DyadicFastLog.check 155907312846 1099511627776 2 16 (lift40 out_w26)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w26 : out_w26.Contains (Real.log ((155907312846:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w26

noncomputable def out_w27 : DyadicInterval 40 := ⟨-168131232448,-168131232384⟩
theorem checked_w27 : DyadicFastLog.check 943604314930 1099511627776 0 16 (lift40 out_w27)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w27 : out_w27.Contains (Real.log ((943604314930:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w27

noncomputable def out_w28 : DyadicInterval 40 := ⟨-165781580672,-165781580608⟩
theorem checked_w28 : DyadicFastLog.check 945622949562 1099511627776 0 16 (lift40 out_w28)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w28 : out_w28.Contains (Real.log ((945622949562:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w28

noncomputable def out_w29 : DyadicInterval 40 := ⟨78662794688,78662794752⟩
theorem checked_w29 : DyadicFastLog.check 1099511627776 1181056647168 0 16 (lift40 out_w29.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w29 : out_w29.Contains (Real.log ((1181056647168:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w29

noncomputable def out_w30 : DyadicInterval 40 := ⟨-84727255616,-84727255552⟩
theorem checked_w30 : DyadicFastLog.check 1017966608384 1099511627776 0 16 (lift40 out_w30)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w30 : out_w30.Contains (Real.log ((1017966608384:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w30

noncomputable def out_w31 : DyadicInterval 40 := ⟨83897544128,83897544192⟩
theorem checked_w31 : DyadicFastLog.check 1099511627776 1186693037312 0 16 (lift40 out_w31.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w31 : out_w31.Contains (Real.log ((1186693037312:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w31

noncomputable def out_w32 : DyadicInterval 40 := ⟨-90832069824,-90832069760⟩
theorem checked_w32 : DyadicFastLog.check 1012330218240 1099511627776 0 16 (lift40 out_w32)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w32 : out_w32.Contains (Real.log ((1012330218240:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w32

noncomputable def out_w33 : DyadicInterval 40 := ⟨-6934525632,-6934525568⟩
theorem checked_w33 : DyadicFastLog.check 1092598924011 1099511627776 0 16 (lift40 out_w33)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w33 : out_w33.Contains (Real.log ((1092598924011:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w33

noncomputable def out_w34 : DyadicInterval 40 := ⟨-6064460928,-6064460864⟩
theorem checked_w34 : DyadicFastLog.check 1093463860732 1099511627776 0 16 (lift40 out_w34)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w34 : out_w34.Contains (Real.log ((1093463860732:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w34

noncomputable def out_w35 : DyadicInterval 40 := ⟨163390050304,163390050368⟩
theorem checked_w35 : DyadicFastLog.check 1099511627776 1275666122962 0 16 (lift40 out_w35.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w35 : out_w35.Contains (Real.log ((1275666122962:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w35

noncomputable def out_w36 : DyadicInterval 40 := ⟨174729613952,174729614016⟩
theorem checked_w36 : DyadicFastLog.check 1099511627776 1288890492072 0 16 (lift40 out_w36.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w36 : out_w36.Contains (Real.log ((1288890492072:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w36

noncomputable def out_w37 : DyadicInterval 40 := ⟨2411110045440,2411110103296⟩
theorem checked_w37 : DyadicFastLog.check 1099511627776 9852822096294 3 16 (lift40 out_w37.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w37 : out_w37.Contains (Real.log ((9852822096294:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w37

noncomputable def out_w38 : DyadicInterval 40 := ⟨2415873968064,2415874025920⟩
theorem checked_w38 : DyadicFastLog.check 1099511627776 9895604650045 3 16 (lift40 out_w38.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w38 : out_w38.Contains (Real.log ((9895604650045:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w38

noncomputable def out_w39 : DyadicInterval 40 := ⟨1979610472128,1979610510720⟩
theorem checked_w39 : DyadicFastLog.check 1099511627776 6654619961989 2 16 (lift40 out_w39.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w39 : out_w39.Contains (Real.log ((6654619961989:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w39

noncomputable def out_w40 : DyadicInterval 40 := ⟨1996289190272,1996289228864⟩
theorem checked_w40 : DyadicFastLog.check 1099511627776 6756334777855 2 16 (lift40 out_w40.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w40 : out_w40.Contains (Real.log ((6756334777855:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w40

end LaneCBRB2Cell000000Endpoints

namespace GeneralCK.Certificates.LaneCB.RB2Cell000000
open Set LaneCBRB2Cell000000Endpoints
open BivariateJetProgram (RegistersContain RegistersSound zeroBox zeroJet)
open BivariateProvedProgram
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
theorem lc0 : ProvedTranscendental.LogEncloses (⟨110165911142,110165911143⟩ : DyadicInterval 40) (⟨-2529573748800,-2529573690944⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w1
theorem lc1 : ProvedTranscendental.LogEncloses (⟨989345716633,989345716634⟩ : DyadicInterval 40) (⟨-116083747264,-116083747200⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w2
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w3
theorem lc2 : ProvedTranscendental.LogEncloses (⟨154897618042,154897618044⟩ : DyadicInterval 40) (⟨-2154885614464,-2154885574912⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w4
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w5
theorem lc3 : ProvedTranscendental.LogEncloses (⟨944614009732,944614009734⟩ : DyadicInterval 40) (⟨-166955339520,-166955339456⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w6
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w7
theorem lc4 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
theorem lc5 : ProvedTranscendental.LogEncloses (⟨1183858768896,1183858768896⟩ : DyadicInterval 40) (⟨81268356672,81268356736⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w9
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w9
theorem lc6 : ProvedTranscendental.LogEncloses (⟨1015164486656,1015164486656⟩ : DyadicInterval 40) (⟨-87758016768,-87758016704⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w10
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w10
theorem lc7 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
theorem lc8 : ProvedTranscendental.LogEncloses (⟨1183858902272,1183858902272⟩ : DyadicInterval 40) (⟨81268480576,81268480640⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w11
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w11
theorem lc9 : ProvedTranscendental.LogEncloses (⟨1015164353280,1015164353280⟩ : DyadicInterval 40) (⟨-87758161280,-87758161216⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w12
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w12
theorem lc10 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
theorem lc11 : ProvedTranscendental.LogEncloses (⟨1093041061630,1093041082095⟩ : DyadicInterval 40) (⟨-6489680640,-6489660032⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w13
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w14
theorem lc12 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
theorem lc13 : ProvedTranscendental.LogEncloses (⟨1183858768896,1183858902272⟩ : DyadicInterval 40) (⟨81268356672,81268480640⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w9
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w11
theorem lc14 : ProvedTranscendental.LogEncloses (⟨1015164353280,1015164486656⟩ : DyadicInterval 40) (⟨-87758161280,-87758016704⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w12
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w10
theorem lc15 : ProvedTranscendental.LogEncloses (⟨1093041061630,1093041082095⟩ : DyadicInterval 40) (⟨-6489680640,-6489660032⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w13
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w14
theorem lc16 : ProvedTranscendental.LogEncloses (⟨1282222239996,1282222552920⟩ : DyadicInterval 40) (⟨169026373440,169026641856⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w15
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w16
theorem lc17 : ProvedTranscendental.LogEncloses (⟨9874171674723,9874171674824⟩ : DyadicInterval 40) (⟨2413489943680,2413490001536⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w17
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w18
theorem lc18 : ProvedTranscendental.LogEncloses (⟨6705165002378,6705165002480⟩ : DyadicInterval 40) (⟨1987930235456,1987930274112⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w19
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w20
theorem lc19 : ProvedTranscendental.LogEncloses (⟨109951162777,110380659508⟩ : DyadicInterval 40) (⟨-2531719137984,-2527432479680⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w21
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w22
theorem lc20 : ProvedTranscendental.LogEncloses (⟨989130968268,989560464999⟩ : DyadicInterval 40) (⟨-116322434304,-115845112064⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w23
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w24
theorem lc21 : ProvedTranscendental.LogEncloses (⟨153888678214,155907312846⟩ : DyadicInterval 40) (⟨-2162070810560,-2147741704512⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w25
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w26
theorem lc22 : ProvedTranscendental.LogEncloses (⟨943604314930,945622949562⟩ : DyadicInterval 40) (⟨-168131232448,-165781580608⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w27
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w28
theorem lc23 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
theorem lc24 : ProvedTranscendental.LogEncloses (⟨1181056647168,1181056647168⟩ : DyadicInterval 40) (⟨78662794688,78662794752⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w29
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w29
theorem lc25 : ProvedTranscendental.LogEncloses (⟨1017966608384,1017966608384⟩ : DyadicInterval 40) (⟨-84727255616,-84727255552⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w30
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w30
theorem lc26 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
theorem lc27 : ProvedTranscendental.LogEncloses (⟨1186693037312,1186693037312⟩ : DyadicInterval 40) (⟨83897544128,83897544192⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w31
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w31
theorem lc28 : ProvedTranscendental.LogEncloses (⟨1012330218240,1012330218240⟩ : DyadicInterval 40) (⟨-90832069824,-90832069760⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w32
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w32
theorem lc29 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
theorem lc30 : ProvedTranscendental.LogEncloses (⟨1092598924011,1093463860732⟩ : DyadicInterval 40) (⟨-6934525632,-6064460864⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w33
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w34
theorem lc31 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
theorem lc32 : ProvedTranscendental.LogEncloses (⟨1181056647168,1186693037312⟩ : DyadicInterval 40) (⟨78662794688,83897544192⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w29
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w31
theorem lc33 : ProvedTranscendental.LogEncloses (⟨1012330218240,1017966608384⟩ : DyadicInterval 40) (⟨-90832069824,-84727255552⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w32
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w30
theorem lc34 : ProvedTranscendental.LogEncloses (⟨1092598924011,1093463860732⟩ : DyadicInterval 40) (⟨-6934525632,-6064460864⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w33
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w34
theorem lc35 : ProvedTranscendental.LogEncloses (⟨1275666122962,1288890492072⟩ : DyadicInterval 40) (⟨163390050304,174729614016⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w35
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w36
theorem lc36 : ProvedTranscendental.LogEncloses (⟨9852822096294,9895604650045⟩ : DyadicInterval 40) (⟨2411110045440,2415874025920⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w37
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w38
theorem lc37 : ProvedTranscendental.LogEncloses (⟨6654619961989,6756334777855⟩ : DyadicInterval 40) (⟨1979610472128,1996289228864⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w39
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w40
theorem ew11_ok (x : ℝ) (hx : (⟨84347141120,84347141120⟩ : DyadicInterval 40).Contains x) : (⟨758884930015,758884949345⟩ : DyadicInterval 40).Contains (Reflection.biasE x) := by
  exact ProvedTranscendental.entropy_encloses (c:=(⟨84347141120,84347141120⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (plus:=(⟨81268356672,81268356736⟩ : DyadicInterval 40)) (minus:=(⟨-87758016768,-87758016704⟩ : DyadicInterval 40))
    (lc4 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc5 lc6 (by decide) hx
theorem ew14_ok (x : ℝ) (hx : (⟨84347274496,84347274496⟩ : DyadicInterval 40).Contains x) : (⟨758884919772,758884939102⟩ : DyadicInterval 40).Contains (Reflection.biasE x) := by
  exact ProvedTranscendental.entropy_encloses (c:=(⟨84347274496,84347274496⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (plus:=(⟨81268480576,81268480640⟩ : DyadicInterval 40)) (minus:=(⟨-87758161280,-87758161216⟩ : DyadicInterval 40))
    (lc7 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc8 lc9 (by decide) hx
theorem ew35_ok (x : ℝ) (hx : (⟨81545019392,81545019392⟩ : DyadicInterval 40).Contains x) : (⟨759096721829,759096741158⟩ : DyadicInterval 40).Contains (Reflection.biasE x) := by
  exact ProvedTranscendental.entropy_encloses (c:=(⟨81545019392,81545019392⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (plus:=(⟨78662794688,78662794752⟩ : DyadicInterval 40)) (minus:=(⟨-84727255616,-84727255552⟩ : DyadicInterval 40))
    (lc23 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc24 lc25 (by decide) hx
theorem ew38_ok (x : ℝ) (hx : (⟨87181409536,87181409536⟩ : DyadicInterval 40).Contains x) : (⟨758663400863,758663420192⟩ : DyadicInterval 40).Contains (Reflection.biasE x) := by
  exact ProvedTranscendental.entropy_encloses (c:=(⟨87181409536,87181409536⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (plus:=(⟨83897544128,83897544192⟩ : DyadicInterval 40)) (minus:=(⟨-90832069824,-90832069760⟩ : DyadicInterval 40))
    (lc26 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc27 lc28 (by decide) hx
theorem bw17_ok (x : ℝ) (hx : (⟨84347141120,84347274496⟩ : DyadicInterval 40).Contains x) : (⟨765368213632,765368243200⟩ : DyadicInterval 40).Contains (Reflection.biasB x) := by
  exact ProvedTranscendental.denominator_encloses (c:=(⟨84347141120,84347274496⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (gapLog:=(⟨-6489680640,-6489660032⟩ : DyadicInterval 40))
    (lc10 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc11 (by decide) hx
theorem bw41_ok (x : ℝ) (hx : (⟨81545019392,87181409536⟩ : DyadicInterval 40).Contains x) : (⟨765155614048,765590665696⟩ : DyadicInterval 40).Contains (Reflection.biasB x) := by
  exact ProvedTranscendental.denominator_encloses (c:=(⟨81545019392,87181409536⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (gapLog:=(⟨-6934525632,-6064460864⟩ : DyadicInterval 40))
    (lc29 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc30 (by decide) hx
theorem brcenter28_contact (y : ℝ) (hy : (⟨9892476781852,9892476923754⟩ : DyadicInterval 40).Contains y) : (⟨84347141120,84347274496⟩ : DyadicInterval 40).Contains (Reflection.biasContact y) := by
  exact ProvedTranscendental.contact_bracket (Y:=(⟨9892476781852,9892476923754⟩ : DyadicInterval 40)) (c:=(⟨84347141120,84347274496⟩ : DyadicInterval 40)) (elo:=(⟨758884930015,758884949345⟩ : DyadicInterval 40)) (ehi:=(⟨758884919772,758884939102⟩ : DyadicInterval 40))
    (by decide) (by decide) (by decide) (by decide)
    (ew11_ok _ (DyadicContact.point_contains 40 84347141120)) (ew14_ok _ (DyadicContact.point_contains 40 84347274496))
    (by decide) (by decide) hy
theorem brcenter28_jet (y : ℝ) (hy : (⟨9892476781852,9892476923754⟩ : DyadicInterval 40).Contains y) : (⟨⟨84347141120,84347274496⟩,⟨-9295477117,-9295447358⟩,⟨2040091289,2040101250⟩⟩ : DyadicJetEnclosure 40).Contains reflectionContactJet y := by
  exact ProvedTranscendental.contact_jet (c:=(⟨84347141120,84347274496⟩ : DyadicInterval 40)) (B:=(⟨765368213632,765368243200⟩ : DyadicInterval 40)) (by decide) brcenter28_contact bw17_ok (by decide) (by decide) (by decide) hy
theorem brwhole28_contact (y : ℝ) (hy : (⟨9568093425736,10235266268244⟩ : DyadicInterval 40).Contains y) : (⟨81545019392,87181409536⟩ : DyadicInterval 40).Contains (Reflection.biasContact y) := by
  exact ProvedTranscendental.contact_bracket (Y:=(⟨9568093425736,10235266268244⟩ : DyadicInterval 40)) (c:=(⟨81545019392,87181409536⟩ : DyadicInterval 40)) (elo:=(⟨759096721829,759096741158⟩ : DyadicInterval 40)) (ehi:=(⟨758663400863,758663420192⟩ : DyadicInterval 40))
    (by decide) (by decide) (by decide) (by decide)
    (ew35_ok _ (DyadicContact.point_contains 40 81545019392)) (ew38_ok _ (DyadicContact.point_contains 40 87181409536))
    (by decide) (by decide) hy
theorem brwhole28_jet (y : ℝ) (hy : (⟨9568093425736,10235266268244⟩ : DyadicInterval 40).Contains y) : (⟨⟨81545019392,87181409536⟩,⟨-9933401820,-8685568522⟩,⟨1839954362,2256264278⟩⟩ : DyadicJetEnclosure 40).Contains reflectionContactJet y := by
  exact ProvedTranscendental.contact_jet (c:=(⟨81545019392,87181409536⟩ : DyadicInterval 40)) (B:=(⟨765155614048,765590665696⟩ : DyadicInterval 40)) (by decide) brwhole28_contact bw41_ok (by decide) (by decide) (by decide) hy
noncomputable def centerInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨110165911142,110165911143⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨111883898060,111883898061⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
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
noncomputable def centerStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-110165911143,-110165911142⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes3 := centerStep2.proposed :: centerBoxes2
theorem centerAccepted2 : StepValid centerStep2.shape centerBoxes2 centerStep2.proposed := by
  dsimp only [StepValid,centerStep2]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨439589902745,439589902746⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes4 := centerStep3.proposed :: centerBoxes3
theorem centerAccepted3 : StepValid centerStep3.shape centerBoxes3 centerStep3.proposed := by
  dsimp only [StepValid,centerStep3]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨44731706900,44731706901⟩,⟨-111883898061,-111883898060⟩,⟨439589902745,439589902746⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes5 := centerStep4.proposed :: centerBoxes4
theorem centerAccepted4 : StepValid centerStep4.shape centerBoxes4 centerStep4.proposed := by
  dsimp only [StepValid,centerStep4]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨154897618042,154897618044⟩,⟨987627729715,987627729716⟩,⟨439589902745,439589902746⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes6 := centerStep5.proposed :: centerBoxes5
theorem centerAccepted5 : StepValid centerStep5.shape centerBoxes5 centerStep5.proposed := by
  dsimp only [StepValid,centerStep5]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨44731706899,44731706902⟩,⟨-111883898061,-111883898060⟩,⟨439589902745,439589902746⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes7 := centerStep6.proposed :: centerBoxes6
theorem centerAccepted6 : StepValid centerStep6.shape centerBoxes6 centerStep6.proposed := by
  dsimp only [StepValid,centerStep6]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep7 : Instruction 40 := ⟨.log 7,⟨⟨-2529573748800,-2529573690944⟩,⟨10973683302499,10973683302600⟩,⟨0,0⟩,⟨-109522921071186,-109522921069169⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes8 := centerStep7.proposed :: centerBoxes7
theorem centerAccepted7 : StepValid centerStep7.shape centerBoxes7 centerStep7.proposed := by
  dsimp only [StepValid,centerStep7]
  exact ⟨by decide,by decide,lc0,by decide⟩
noncomputable def centerStep8 : Instruction 40 := ⟨.mul 8 0,⟨⟨-253451432255,-253451426454⟩,⟨-1430062121035,-1430062063157⟩,⟨0,0⟩,⟨10973683302297,10973683302802⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes9 := centerStep8.proposed :: centerBoxes8
theorem centerAccepted8 : StepValid centerStep8.shape centerBoxes8 centerStep8.proposed := by
  dsimp only [StepValid,centerStep8]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep9 : Instruction 40 := ⟨.neg 0,⟨⟨253451426454,253451432255⟩,⟨1430062063157,1430062121035⟩,⟨0,0⟩,⟨-10973683302802,-10973683302297⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes10 := centerStep9.proposed :: centerBoxes9
theorem centerAccepted9 : StepValid centerStep9.shape centerBoxes9 centerStep9.proposed := by
  dsimp only [StepValid,centerStep9]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep10 : Instruction 40 := ⟨.add 12 7,⟨⟨989345716633,989345716634⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes11 := centerStep10.proposed :: centerBoxes10
theorem centerAccepted10 : StepValid centerStep10.shape centerBoxes10 centerStep10.proposed := by
  dsimp only [StepValid,centerStep10]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep11 : Instruction 40 := ⟨.log 0,⟨⟨-116083747264,-116083747200⟩,⟨-1221944765405,-1221944765402⟩,⟨0,0⟩,⟨-1358011113281,-1358011113273⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes12 := centerStep11.proposed :: centerBoxes11
theorem centerAccepted11 : StepValid centerStep11.shape centerBoxes11 centerStep11.proposed := by
  dsimp only [StepValid,centerStep11]
  exact ⟨by decide,by decide,lc1,by decide⟩
noncomputable def centerStep12 : Instruction 40 := ⟨.mul 1 0,⟨⟨-104452699931,-104452699873⟩,⟨-983427880578,-983427880510⟩,⟨0,0⟩,⟨1221944765396,1221944765411⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes13 := centerStep12.proposed :: centerBoxes12
theorem centerAccepted12 : StepValid centerStep12.shape centerBoxes12 centerStep12.proposed := by
  dsimp only [StepValid,centerStep12]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep13 : Instruction 40 := ⟨.neg 0,⟨⟨104452699873,104452699931⟩,⟨983427880510,983427880578⟩,⟨0,0⟩,⟨-1221944765411,-1221944765396⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes14 := centerStep13.proposed :: centerBoxes13
theorem centerAccepted13 : StepValid centerStep13.shape centerBoxes13 centerStep13.proposed := by
  dsimp only [StepValid,centerStep13]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep14 : Instruction 40 := ⟨.add 4 0,⟨⟨357904126327,357904132186⟩,⟨2413489943667,2413490001613⟩,⟨0,0⟩,⟨-12195628068213,-12195628067693⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes15 := centerStep14.proposed :: centerBoxes14
theorem centerAccepted14 : StepValid centerStep14.shape centerBoxes14 centerStep14.proposed := by
  dsimp only [StepValid,centerStep14]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2154885614464,-2154885574912⟩,⟨7010489808998,7010489809097⟩,⟨3120346301153,3120346301201⟩,⟨-44698906425268,-44698906424007⟩,⟨-27700015063075,-27700015062386⟩,⟨-8855350678840,-8855350678567⟩⟩⟩
noncomputable def centerBoxes16 := centerStep15.proposed :: centerBoxes15
theorem centerAccepted15 : StepValid centerStep15.shape centerBoxes15 centerStep15.proposed := by
  dsimp only [StepValid,centerStep15]
  exact ⟨by decide,by decide,lc2,by decide⟩
noncomputable def centerStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-303577188641,-303577183064⟩,⟨-947981438448,-947981402891⟩,⟨-421943466951,-421943451122⟩,⟨6297117701302,6297117701753⟩,⟨3858200634342,3858200674137⟩,⟨1247529077784,1247529077884⟩⟩⟩
noncomputable def centerBoxes17 := centerStep16.proposed :: centerBoxes16
theorem centerAccepted16 : StepValid centerStep16.shape centerBoxes16 centerStep16.proposed := by
  dsimp only [StepValid,centerStep16]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep17 : Instruction 40 := ⟨.neg 0,⟨⟨303577183064,303577188641⟩,⟨947981402891,947981438448⟩,⟨421943451122,421943466951⟩,⟨-6297117701753,-6297117701302⟩,⟨-3858200674137,-3858200634342⟩,⟨-1247529077884,-1247529077784⟩⟩⟩
noncomputable def centerBoxes18 := centerStep17.proposed :: centerBoxes17
theorem centerAccepted17 : StepValid centerStep17.shape centerBoxes17 centerStep17.proposed := by
  dsimp only [StepValid,centerStep17]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-154897618044,-154897618042⟩,⟨-987627729716,-987627729715⟩,⟨-439589902746,-439589902745⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes19 := centerStep18.proposed :: centerBoxes18
theorem centerAccepted18 : StepValid centerStep18.shape centerBoxes18 centerStep18.proposed := by
  dsimp only [StepValid,centerStep18]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨944614009732,944614009734⟩,⟨-987627729716,-987627729715⟩,⟨-439589902746,-439589902745⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes20 := centerStep19.proposed :: centerBoxes19
theorem centerAccepted19 : StepValid centerStep19.shape centerBoxes19 centerStep19.proposed := by
  dsimp only [StepValid,centerStep19]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep20 : Instruction 40 := ⟨.log 0,⟨⟨-166955339520,-166955339456⟩,⟨-1149578729037,-1149578729031⟩,⟨-511673767849,-511673767846⟩,⟨-1201925673971,-1201925673959⟩,⟨744836103071,744836103081⟩,⟨-238114848530,-238114848527⟩⟩⟩
noncomputable def centerBoxes21 := centerStep20.proposed :: centerBoxes20
theorem centerAccepted20 : StepValid centerStep20.shape centerBoxes20 centerStep20.proposed := by
  dsimp only [StepValid,centerStep20]
  exact ⟨by decide,by decide,lc3,by decide⟩
noncomputable def centerStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-143434911216,-143434911160⟩,⟨-837661400393,-837661400326⟩,⟨-372840375431,-372840375399⟩,⟨1032600112258,1032600112285⟩,⟨1392163252765,1392163252848⟩,⟨204569570852,204569570861⟩⟩⟩
noncomputable def centerBoxes22 := centerStep21.proposed :: centerBoxes21
theorem centerAccepted21 : StepValid centerStep21.shape centerBoxes21 centerStep21.proposed := by
  dsimp only [StepValid,centerStep21]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep22 : Instruction 40 := ⟨.neg 0,⟨⟨143434911160,143434911216⟩,⟨837661400326,837661400393⟩,⟨372840375399,372840375431⟩,⟨-1032600112285,-1032600112258⟩,⟨-1392163252848,-1392163252765⟩,⟨-204569570861,-204569570852⟩⟩⟩
noncomputable def centerBoxes23 := centerStep22.proposed :: centerBoxes22
theorem centerAccepted22 : StepValid centerStep22.shape centerBoxes22 centerStep22.proposed := by
  dsimp only [StepValid,centerStep22]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨447012094224,447012099857⟩,⟨1785642803217,1785642838841⟩,⟨794783826521,794783842382⟩,⟨-7329717814038,-7329717813560⟩,⟨-5250363926985,-5250363887107⟩,⟨-1452098648745,-1452098648636⟩⟩⟩
noncomputable def centerBoxes24 := centerStep23.proposed :: centerBoxes23
theorem centerAccepted23 : StepValid centerStep23.shape centerBoxes23 centerStep23.proposed := by
  dsimp only [StepValid,centerStep23]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨804916220551,804916232043⟩,⟨4199132746884,4199132840454⟩,⟨794783826521,794783842382⟩,⟨-19525345882251,-19525345881253⟩,⟨-5250363926985,-5250363887107⟩,⟨-1452098648745,-1452098648636⟩⟩⟩
noncomputable def centerBoxes25 := centerStep24.proposed :: centerBoxes24
theorem centerAccepted24 : StepValid centerStep24.shape centerBoxes24 centerStep24.proposed := by
  dsimp only [StepValid,centerStep24]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨89463413798,89463413804⟩,⟨-223767796122,-223767796120⟩,⟨879179805490,879179805492⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes26 := centerStep25.proposed :: centerBoxes25
theorem centerAccepted25 : StepValid centerStep25.shape centerBoxes25 centerStep25.proposed := by
  dsimp only [StepValid,centerStep25]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep26 : Instruction 40 := ⟨.inv 0,⟨⟨13513074990221,13513074991128⟩,⟨33799190985386,33799190990226⟩,⟨-132796437537296,-132796437519166⟩,⟨169078512787550,169078512824621⟩,⟨-332153278129136,-332153277943327⟩,⟨2610048983009966,2610048983547418⟩⟩⟩
noncomputable def centerBoxes27 := centerStep26.proposed :: centerBoxes26
theorem centerAccepted26 : StepValid centerStep26.shape centerBoxes26 centerStep26.proposed := by
  dsimp only [StepValid,centerStep26]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨9892476781852,9892476923754⟩,⟨76350909483312,76350910993568⟩,⟨-87447947118982,-87447945522143⟩,⟨141973172253173,141973179865568⟩,⟨-790415431931230,-790415415967656⟩,⟨1700900174147398,1700900205680914⟩⟩⟩
noncomputable def centerBoxes28 := centerStep27.proposed :: centerBoxes27
theorem centerAccepted27 : StepValid centerStep27.shape centerBoxes27 centerStep27.proposed := by
  dsimp only [StepValid,centerStep27]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep28 : Instruction 40 := ⟨.contact 0,⟨⟨84347141120,84347274496⟩,⟨-645484893542,-645482814286⟩,⟨739298933846,739301314182⟩,⟨8637087924716,8637140253067⟩,⟨-4584899107371,-4584822137342⟩,⟨-1474991376412,-1474881593523⟩⟩⟩
noncomputable def centerBoxes29 := centerStep28.proposed :: centerBoxes28
theorem centerAccepted28 : StepValid centerStep28.shape centerBoxes28 centerStep28.proposed := by
  dsimp only [StepValid,centerStep28]
  exact ⟨by decide,by decide,(⟨⟨84347141120,84347274496⟩,⟨-9295477117,-9295447358⟩,⟨2040091289,2040101250⟩⟩ : DyadicJetEnclosure 40),brcenter28_jet,by decide⟩
noncomputable def centerStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes30 := centerStep29.proposed :: centerBoxes29
theorem centerAccepted29 : StepValid centerStep29.shape centerBoxes29 centerStep29.proposed := by
  dsimp only [StepValid,centerStep29]
  exact ⟨by decide,by decide,lc4,by decide⟩
noncomputable def centerStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1183858768896,1183858902272⟩,⟨-645484893542,-645482814286⟩,⟨739298933846,739301314182⟩,⟨8637087924716,8637140253067⟩,⟨-4584899107371,-4584822137342⟩,⟨-1474991376412,-1474881593523⟩⟩⟩
noncomputable def centerBoxes31 := centerStep30.proposed :: centerBoxes30
theorem centerAccepted30 : StepValid centerStep30.shape centerBoxes30 centerStep30.proposed := by
  dsimp only [StepValid,centerStep30]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep31 : Instruction 40 := ⟨.log 0,⟨⟨81268356672,81268480640⟩,⟨-599495619453,-599493620797⟩,⟨686625553607,686627841708⟩,⟨7694847060038,7694898743349⟩,⟨-3883862718063,-3883788256544⟩,⟨-1798690089486,-1798585116281⟩⟩⟩
noncomputable def centerBoxes32 := centerStep31.proposed :: centerBoxes31
theorem centerAccepted31 : StepValid centerStep31.shape centerBoxes31 centerStep31.proposed := by
  dsimp only [StepValid,centerStep31]
  exact ⟨by decide,by decide,lc13,by decide⟩
noncomputable def centerStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨87502718706,87502862043⟩,⟨-693194854228,-693192403063⟩,⟨793942756016,793945562231⟩,⟨9627419575197,9627485612364⟩,⟨-5326882307547,-5326790173225⟩,⟨-1122336928820,-1122209353932⟩⟩⟩
noncomputable def centerBoxes33 := centerStep32.proposed :: centerBoxes32
theorem centerAccepted32 : StepValid centerStep32.shape centerBoxes32 centerStep32.proposed := by
  dsimp only [StepValid,centerStep32]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-84347274496,-84347141120⟩,⟨645482814286,645484893542⟩,⟨-739301314182,-739298933846⟩,⟨-8637140253067,-8637087924716⟩,⟨4584822137342,4584899107371⟩,⟨1474881593523,1474991376412⟩⟩⟩
noncomputable def centerBoxes34 := centerStep33.proposed :: centerBoxes33
theorem centerAccepted33 : StepValid centerStep33.shape centerBoxes33 centerStep33.proposed := by
  dsimp only [StepValid,centerStep33]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1015164353280,1015164486656⟩,⟨645482814286,645484893542⟩,⟨-739301314182,-739298933846⟩,⟨-8637140253067,-8637087924716⟩,⟨4584822137342,4584899107371⟩,⟨1474881593523,1474991376412⟩⟩⟩
noncomputable def centerBoxes35 := centerStep34.proposed :: centerBoxes34
theorem centerAccepted34 : StepValid centerStep34.shape centerBoxes34 centerStep34.proposed := by
  dsimp only [StepValid,centerStep34]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep35 : Instruction 40 := ⟨.log 0,⟨⟨-87758161280,-87758016704⟩,⟨699114152598,699116496468⟩,⟨-800727871056,-800725187741⟩,⟨-9799305151075,-9799244265170⟩,⟨5474895617407,5474983048200⟩,⟨1014289043847,1014412066465⟩⟩⟩
noncomputable def centerBoxes36 := centerStep35.proposed :: centerBoxes35
theorem centerAccepted35 : StepValid centerStep35.shape centerBoxes35 centerStep35.proposed := by
  dsimp only [StepValid,centerStep35]
  exact ⟨by decide,by decide,lc14,by decide⟩
noncomputable def centerStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-81025945061,-81025800930⟩,⟨593962976563,593965476267⟩,⟨-680293933316,-680291071514⟩,⟨-7537346878467,-7537278766144⟩,⟨3748792609432,3748886922548⟩,⟨1895548944356,1895678684321⟩⟩⟩
noncomputable def centerBoxes37 := centerStep36.proposed :: centerBoxes36
theorem centerAccepted36 : StepValid centerStep36.shape centerBoxes36 centerStep36.proposed := by
  dsimp only [StepValid,centerStep36]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨6476773645,6477061113⟩,⟨-99231877665,-99226926796⟩,⟨113648822700,113654490717⟩,⟨2090072696730,2090206846220⟩,⟨-1578089698115,-1577903250677⟩,⟨773212015536,773469330389⟩⟩⟩
noncomputable def centerBoxes38 := centerStep37.proposed :: centerBoxes37
theorem centerAccepted37 : StepValid centerStep37.shape centerBoxes37 centerStep37.proposed := by
  dsimp only [StepValid,centerStep37]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨3238386822,3238530557⟩,⟨-49615938833,-49613463398⟩,⟨56824411350,56827245359⟩,⟨1045036348365,1045103423110⟩,⟨-789044849058,-788951625338⟩,⟨386606007768,386734665195⟩⟩⟩
noncomputable def centerBoxes39 := centerStep38.proposed :: centerBoxes38
theorem centerAccepted38 : StepValid centerStep38.shape centerBoxes38 centerStep38.proposed := by
  dsimp only [StepValid,centerStep38]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-3238530557,-3238386822⟩,⟨49613463398,49615938833⟩,⟨-56827245359,-56824411350⟩,⟨-1045103423110,-1045036348365⟩,⟨788951625338,789044849058⟩,⟨-386734665195,-386606007768⟩⟩⟩
noncomputable def centerBoxes40 := centerStep39.proposed :: centerBoxes39
theorem centerAccepted39 : StepValid centerStep39.shape centerBoxes39 centerStep39.proposed := by
  dsimp only [StepValid,centerStep39]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨758884853059,758885016058⟩,⟨49613463398,49615938833⟩,⟨-56827245359,-56824411350⟩,⟨-1045103423110,-1045036348365⟩,⟨788951625338,789044849058⟩,⟨-386734665195,-386606007768⟩⟩⟩
noncomputable def centerBoxes41 := centerStep40.proposed :: centerBoxes40
theorem centerAccepted40 : StepValid centerStep40.shape centerBoxes40 centerStep40.proposed := by
  dsimp only [StepValid,centerStep40]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨6470545681,6470566146⟩,⟨-99034680714,-99034205098⟩,⟨113428089212,113428633782⟩,⟨2083037066022,2083052072662⟩,⟨-1571482377816,-1571463865266⟩,⟨767888943445,767912546958⟩⟩⟩
noncomputable def centerBoxes42 := centerStep41.proposed :: centerBoxes41
theorem centerAccepted41 : StepValid centerStep41.shape centerBoxes41 centerStep41.proposed := by
  dsimp only [StepValid,centerStep41]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-6470566146,-6470545681⟩,⟨99034205098,99034680714⟩,⟨-113428633782,-113428089212⟩,⟨-2083052072662,-2083037066022⟩,⟨1571463865266,1571482377816⟩,⟨-767912546958,-767888943445⟩⟩⟩
noncomputable def centerBoxes43 := centerStep42.proposed :: centerBoxes42
theorem centerAccepted42 : StepValid centerStep42.shape centerBoxes42 centerStep42.proposed := by
  dsimp only [StepValid,centerStep42]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1093041061630,1093041082095⟩,⟨99034205098,99034680714⟩,⟨-113428633782,-113428089212⟩,⟨-2083052072662,-2083037066022⟩,⟨1571463865266,1571482377816⟩,⟨-767912546958,-767888943445⟩⟩⟩
noncomputable def centerBoxes44 := centerStep43.proposed :: centerBoxes43
theorem centerAccepted43 : StepValid centerStep43.shape centerBoxes43 centerStep43.proposed := by
  dsimp only [StepValid,centerStep43]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep44 : Instruction 40 := ⟨.log 0,⟨⟨-6489680640,-6489660032⟩,⟨99620464259,99620944557⟩,⟨-114100106707,-114099556775⟩,⟨-2104409417303,-2104394195556⟩,⟨1591104469798,1591123221207⟩,⟨-784298983641,-784275111799⟩⟩⟩
noncomputable def centerBoxes45 := centerStep44.proposed :: centerBoxes44
theorem centerAccepted44 : StepValid centerStep44.shape centerBoxes44 centerStep44.proposed := by
  dsimp only [StepValid,centerStep44]
  exact ⟨by decide,by decide,lc11,by decide⟩
noncomputable def centerStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-3244840320,-3244830016⟩,⟨49810232129,49810472279⟩,⟨-57050053354,-57049778387⟩,⟨-1052204708652,-1052197097778⟩,⟨795552234899,795561610604⟩,⟨-392149491821,-392137555899⟩⟩⟩
noncomputable def centerBoxes46 := centerStep45.proposed :: centerBoxes45
theorem centerAccepted45 : StepValid centerStep45.shape centerBoxes45 centerStep45.proposed := by
  dsimp only [StepValid,centerStep45]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3244830016,3244840320⟩,⟨-49810472279,-49810232129⟩,⟨57049778387,57050053354⟩,⟨1052197097778,1052204708652⟩,⟨-795561610604,-795552234899⟩,⟨392137555899,392149491821⟩⟩⟩
noncomputable def centerBoxes47 := centerStep46.proposed :: centerBoxes46
theorem centerAccepted46 : StepValid centerStep46.shape centerBoxes46 centerStep46.proposed := by
  dsimp only [StepValid,centerStep46]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765368213632,765368243200⟩,⟨-49810472279,-49810232129⟩,⟨57049778387,57050053354⟩,⟨1052197097778,1052204708652⟩,⟨-795561610604,-795552234899⟩,⟨392137555899,392149491821⟩⟩⟩
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
noncomputable def centerStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨273260265407,273260270524⟩,⟨24758551274,24758670179⟩,⟨-28357158446,-28357022303⟩,⟨-520763018166,-520759266505⟩,⟨392865966316,392870594454⟩,⟨-191978136740,-191972235861⟩⟩⟩
noncomputable def centerBoxes51 := centerStep50.proposed :: centerBoxes50
theorem centerAccepted50 : StepValid centerStep50.shape centerBoxes50 centerStep50.proposed := by
  dsimp only [StepValid,centerStep50]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1530736427264,1530736486400⟩,⟨-99620944558,-99620464258⟩,⟨114099556774,114100106708⟩,⟨2104394195556,2104409417304⟩,⟨-1591123221208,-1591104469798⟩,⟨784275111798,784298983642⟩⟩⟩
noncomputable def centerBoxes52 := centerStep51.proposed :: centerBoxes51
theorem centerAccepted51 : StepValid centerStep51.shape centerBoxes51 centerStep51.proposed := by
  dsimp only [StepValid,centerStep51]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1190866933886,1190867090348⟩,⟨-757204204968,-757201566867⟩,⟨867255175044,867258195254⟩,⟨11094895220798,11094965851573⟩,⟨-6481324492883,-6481225249474⟩,⟨-467113727052,-466975856525⟩⟩⟩
noncomputable def centerBoxes53 := centerStep52.proposed :: centerBoxes52
theorem centerAccepted52 : StepValid centerStep52.shape centerBoxes52 centerStep52.proposed := by
  dsimp only [StepValid,centerStep52]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1282222239996,1282222552920⟩,⟨-1514408409936,-1514403133734⟩,⟨1734510350088,1734516390507⟩,⟨22189790441606,22189931703138⟩,⟨-12962648985762,-12962450498953⟩,⟨-934227300874,-933951866281⟩⟩⟩
noncomputable def centerBoxes54 := centerStep53.proposed :: centerBoxes53
theorem centerAccepted53 : StepValid centerStep53.shape centerBoxes53 centerStep53.proposed := by
  dsimp only [StepValid,centerStep53]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep54 : Instruction 40 := ⟨.log 0,⟨⟨169026373440,169026641856⟩,⟨-1298612365305,-1298607524011⟩,⟨1487350455718,1487355998394⟩,⟨17494079003781,17494216215859⟩,⟨-9358857825834,-9358671814403⟩,⟨-2813113846823,-2812862469302⟩⟩⟩
noncomputable def centerBoxes55 := centerStep54.proposed :: centerBoxes54
theorem centerAccepted54 : StepValid centerStep54.shape centerBoxes54 centerStep54.proposed := by
  dsimp only [StepValid,centerStep54]
  exact ⟨by decide,by decide,lc16,by decide⟩
noncomputable def centerStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨58216544671,58216649232⟩,⟨-441708889414,-441707162698⟩,⟨505906009051,505907985865⟩,⟨5822904219992,5822949983970⟩,⟨-3037263974958,-3037199380123⟩,⟨-1124129797688,-1124039832874⟩⟩⟩
noncomputable def centerBoxes56 := centerStep55.proposed :: centerBoxes55
theorem centerAccepted55 : StepValid centerStep55.shape centerBoxes55 centerStep55.proposed := by
  dsimp only [StepValid,centerStep55]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380432031654,380432053476⟩,⟨9710102004,9710388709⟩,⟨-11121721325,-11121393055⟩,⟨-206488585259,-206479498185⟩,⟨156645331353,156656512879⟩,⟨-78241849140,-78227630515⟩⟩⟩
noncomputable def centerBoxes57 := centerStep56.proposed :: centerBoxes56
theorem centerAccepted56 : StepValid centerStep56.shape centerBoxes56 centerStep56.proposed := by
  dsimp only [StepValid,centerStep56]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3177770665139,3177770847420⟩,⟨-81111440650,-81109036480⟩,⟨92897631213,92900383930⟩,⟨1728875472796,1728951820742⟩,⟨-1313303443961,-1313209613095⟩,⟨658871326178,658990491726⟩⟩⟩
noncomputable def centerBoxes58 := centerStep57.proposed :: centerBoxes57
theorem centerAccepted57 : StepValid centerStep57.shape centerBoxes57 centerStep57.proposed := by
  dsimp only [StepValid,centerStep57]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨168255453792,168255765643⟩,⟨-1280906570279,-1280901371545⟩,⟨1467070846026,1467076797803⟩,⟨16985865165353,16986004789459⟩,⟨-8922374847731,-8922180057637⟩,⟨-3128547858163,-3128278419179⟩⟩⟩
noncomputable def centerBoxes59 := centerStep58.proposed :: centerBoxes58
theorem centerAccepted58 : StepValid centerStep58.shape centerBoxes58 centerStep58.proposed := by
  dsimp only [StepValid,centerStep58]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨337281827232,337282407499⟩,⟨-2579518935584,-2579508895556⟩,⟨2954421301744,2954432796197⟩,⟨34479944169134,34480221005318⟩,⟨-18281232673565,-18280851872040⟩,⟨-5941661704986,-5941140888481⟩⟩⟩
noncomputable def centerBoxes60 := centerStep59.proposed :: centerBoxes59
theorem centerAccepted59 : StepValid centerStep59.shape centerBoxes59 centerStep59.proposed := by
  dsimp only [StepValid,centerStep59]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨523783655992,523783880997⟩,⟨68486598830,68490030642⟩,⟨-78444545592,-78440616666⟩,⟨-1438187304810,-1438093957920⟩,⟨1083942881696,1084072313636⟩,⟨-527976460730,-527798161021⟩⟩⟩
noncomputable def centerBoxes61 := centerStep60.proposed :: centerBoxes60
theorem centerAccepted60 : StepValid centerStep60.shape centerBoxes60 centerStep60.proposed := by
  dsimp only [StepValid,centerStep60]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨361516397617,361516630566⟩,⟨70904355865,70907924061⟩,⟨-81213861779,-81209776707⟩,⟨-1484323918865,-1484226492529⟩,⟨1116899149262,1117033923161⟩,⟨-540534642820,-540349322517⟩⟩⟩
noncomputable def centerBoxes62 := centerStep61.proposed :: centerBoxes61
theorem centerAccepted61 : StepValid centerStep61.shape centerBoxes61 centerStep61.proposed := by
  dsimp only [StepValid,centerStep61]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨723032795234,723033261132⟩,⟨141808711730,141815848122⟩,⟨-162427723558,-162419553414⟩,⟨-2968647837730,-2968452985058⟩,⟨2233798298524,2234067846322⟩,⟨-1081069285640,-1080698645034⟩⟩⟩
noncomputable def centerBoxes63 := centerStep62.proposed :: centerBoxes62
theorem centerAccepted62 : StepValid centerStep62.shape centerBoxes62 centerStep62.proposed := by
  dsimp only [StepValid,centerStep62]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1524265861118,1524265940719⟩,⟨-586739460,-585783544⟩,⟨670922992,672017496⟩,⟨21342122894,21372351282⟩,⟨-19659355942,-19622091982⟩,⟨16362564840,16410040197⟩⟩⟩
noncomputable def centerBoxes64 := centerStep63.proposed :: centerBoxes63
theorem centerAccepted63 : StepValid centerStep63.shape centerBoxes63 centerStep63.proposed := by
  dsimp only [StepValid,centerStep63]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨1002348841433,1002349539659⟩,⟨196205242858,196215775245⟩,⟨-224734274091,-224722215939⟩,⟨-4101588412757,-4101297930020⟩,⟨3083985943022,3084384586035⟩,⟨-1488137722128,-1487592260607⟩⟩⟩
noncomputable def centerBoxes65 := centerStep64.proposed :: centerBoxes64
theorem centerAccepted64 : StepValid centerStep64.shape centerBoxes64 centerStep64.proposed := by
  dsimp only [StepValid,centerStep64]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67913035900,67913038445⟩,⟨12306424272,12306483608⟩,⟨-14095139320,-14095071384⟩,⟨-257734168122,-257732287770⟩,⟨193999899586,194002215960⟩,⟨-93961492653,-93958543741⟩⟩⟩
noncomputable def centerBoxes66 := centerStep65.proposed :: centerBoxes65
theorem centerAccepted65 : StepValid centerStep65.shape centerBoxes65 centerStep65.proposed := by
  dsimp only [StepValid,centerStep65]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨49716895030,49716897604⟩,⟨268375054930,268375113998⟩,⟨38772465006,38772517708⟩,⟨-1300693259248,-1300691379438⟩,⟨-227210800131,-227208784020⟩,⟨-178854625081,-178852363305⟩⟩⟩
noncomputable def centerBoxes67 := centerStep66.proposed :: centerBoxes66
theorem centerAccepted66 : StepValid centerStep66.shape centerBoxes66 centerStep66.proposed := by
  dsimp only [StepValid,centerStep66]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2131086157308,2131086321967⟩,⟨-277383905350,-277382557288⟩,⟨317698046070,317699589578⟩,⟨5877513266311,5877556050083⟩,⟨-4450989089432,-4450936507636⟩,⟨2207411292112,2207478073357⟩⟩⟩
noncomputable def centerBoxes68 := centerStep67.proposed :: centerBoxes67
theorem centerAccepted67 : StepValid centerStep67.shape centerBoxes67 centerStep67.proposed := by
  dsimp only [StepValid,centerStep67]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2966891052555,2966891396412⟩,⟨-579259446558,-579256609028⟩,⟨663447242900,663450491832⟩,⟨12311679671625,12311769855908⟩,⟨-9338156268717,-9338045685381⟩,⟨4659178668181,4659318783827⟩⟩⟩
noncomputable def centerBoxes69 := centerStep68.proposed :: centerBoxes68
theorem centerAccepted68 : StepValid centerStep68.shape centerBoxes68 centerStep68.proposed := by
  dsimp only [StepValid,centerStep68]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨134154662214,134154684709⟩,⟨697983129257,697983502238⟩,⟨134621783622,134622086420⟩,⟨-3235831895260,-3235820861910⟩,⟨-893833734151,-893822244251⟩,⟨-225150307936,-225137509597⟩⟩⟩
noncomputable def centerBoxes70 := centerStep69.proposed :: centerBoxes69
theorem centerAccepted69 : StepValid centerStep69.shape centerBoxes69 centerStep69.proposed := by
  dsimp only [StepValid,centerStep69]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep70 : Instruction 40 := ⟨.inv 0,⟨⟨9011432006544,9011433517579⟩,⟨-46884929848744,-46884889071574⟩,⟨-9042831324316,-9042807952183⟩,⟨705223996208247,705225577053038⟩,⟨154136049801955,154137150998704⟩,⟨33271512213574,33272467745884⟩⟩⟩
noncomputable def centerBoxes71 := centerStep70.proposed :: centerBoxes70
theorem centerAccepted70 : StepValid centerStep70.shape centerBoxes70 centerStep70.proposed := by
  dsimp only [StepValid,centerStep70]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨8215100416611,8215107516674⟩,⟨-41133714735671,-41133561196952⟩,⟨-10085619383277,-10085493198371⟩,⟨592554114097671,592559302264449⟩,⟨173759827325043,173764813855624⟩,⟨21831190001368,21836762685126⟩⟩⟩
noncomputable def centerBoxes72 := centerStep71.proposed :: centerBoxes71
theorem centerAccepted71 : StepValid centerStep71.shape centerBoxes71 centerStep71.proposed := by
  dsimp only [StepValid,centerStep71]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨16430200833222,16430215033348⟩,⟨-82267429471342,-82267122393904⟩,⟨-20171238766554,-20170986396742⟩,⟨1185108228195342,1185118604528898⟩,⟨347519654650086,347529627711248⟩,⟨43662380002736,43673525370252⟩⟩⟩
noncomputable def centerBoxes73 := centerStep72.proposed :: centerBoxes72
theorem centerAccepted72 : StepValid centerStep72.shape centerBoxes72 centerStep72.proposed := by
  dsimp only [StepValid,centerStep72]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10973683302499,10973683302600⟩,⟨-109522921071186,-109522921069169⟩,⟨0,0⟩,⟨2186188521914400,2186188521974786⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes74 := centerStep73.proposed :: centerBoxes73
theorem centerAccepted73 : StepValid centerStep73.shape centerBoxes73 centerStep73.proposed := by
  dsimp only [StepValid,centerStep73]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9874171674723,9874171674824⟩,⟨-109522921071186,-109522921069170⟩,⟨0,0⟩,⟨2186188521914418,2186188521974777⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes75 := centerStep74.proposed :: centerBoxes74
theorem centerAccepted74 : StepValid centerStep74.shape centerBoxes74 centerStep74.proposed := by
  dsimp only [StepValid,centerStep74]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep75 : Instruction 40 := ⟨.log 0,⟨⟨2413489943680,2413490001536⟩,⟨-12195628068220,-12195628067696⟩,⟨0,0⟩,⟨108164909937337,108164909975027⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes76 := centerStep75.proposed :: centerBoxes75
theorem centerAccepted75 : StepValid centerStep75.shape centerBoxes75 centerStep75.proposed := by
  dsimp only [StepValid,centerStep75]
  exact ⟨by decide,by decide,lc17,by decide⟩
noncomputable def centerStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7804676630154,7804676630256⟩,⟨-49762644248138,-49762644246785⟩,⟨-22149191732105,-22149191731474⟩,⟨634573571662061,634573571688241⟩,⟨337846670957669,337846670971128⟩,⟨125716084754158,125716084759663⟩⟩⟩
noncomputable def centerBoxes77 := centerStep76.proposed :: centerBoxes76
theorem centerAccepted76 : StepValid centerStep76.shape centerBoxes76 centerStep76.proposed := by
  dsimp only [StepValid,centerStep76]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6705165002378,6705165002480⟩,⟨-49762644248138,-49762644246785⟩,⟨-22149191732105,-22149191731474⟩,⟨634573571662067,634573571688236⟩,⟨337846670957672,337846670971127⟩,⟨125716084754158,125716084759663⟩⟩⟩
noncomputable def centerBoxes78 := centerStep77.proposed :: centerBoxes77
theorem centerAccepted77 : StepValid centerStep77.shape centerBoxes77 centerStep77.proposed := by
  dsimp only [StepValid,centerStep77]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep78 : Instruction 40 := ⟨.log 0,⟨⟨1987930235456,1987930274112⟩,⟨-8160068538297,-8160068537893⟩,⟨-3632020069123,-3632020068938⟩,⟨43496980743533,43496980757575⟩,⟨28444851162376,28444851169161⟩,⟨8617235828712,8617235831585⟩⟩⟩
noncomputable def centerBoxes79 := centerStep78.proposed :: centerBoxes78
theorem centerAccepted78 : StepValid centerStep78.shape centerBoxes78 centerStep78.proposed := by
  dsimp only [StepValid,centerStep78]
  exact ⟨by decide,by decide,lc18,by decide⟩
noncomputable def centerStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨99127803248,99127803250⟩,⟨879179805490,879179805492⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes80 := centerStep79.proposed :: centerBoxes79
theorem centerAccepted79 : StepValid centerStep79.shape centerBoxes79 centerStep79.proposed := by
  dsimp only [StepValid,centerStep79]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨133075864211,133075864214⟩,⟨709356579173,709356579180⟩,⟨315732315191,315732315196⟩,⟨-1774257784753,-1774257784749⟩,⟨-1579432783384,-1579432783376⟩,⟨-351500207392,-351500207389⟩⟩⟩
noncomputable def centerBoxes81 := centerStep80.proposed :: centerBoxes80
theorem centerAccepted80 : StepValid centerStep80.shape centerBoxes80 centerStep80.proposed := by
  dsimp only [StepValid,centerStep80]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4401420179136,4401420275648⟩,⟨-20355696606517,-20355696605589⟩,⟨-3632020069123,-3632020068938⟩,⟨151661890680870,151661890732602⟩,⟨28444851162376,28444851169161⟩,⟨8617235828712,8617235831585⟩⟩⟩
noncomputable def centerBoxes82 := centerStep81.proposed :: centerBoxes81
theorem centerAccepted81 : StepValid centerStep81.shape centerBoxes81 centerStep81.proposed := by
  dsimp only [StepValid,centerStep81]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨674563654464,674564814998⟩,⟨-5159037871168,-5159017791112⟩,⟨5908842603488,5908865592394⟩,⟨68959888338268,68960442010636⟩,⟨-36562465347130,-36561703744080⟩,⟨-11883323409972,-11882281776962⟩⟩⟩
noncomputable def centerBoxes83 := centerStep82.proposed :: centerBoxes82
theorem centerAccepted82 : StepValid centerStep82.shape centerBoxes82 centerStep82.proposed := by
  dsimp only [StepValid,centerStep82]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5075983833600,5075985090646⟩,⟨-25514734477685,-25514714396701⟩,⟨2276822534365,2276845523456⟩,⟨220621779019138,220622332743238⟩,⟨-8117614184754,-8116852574919⟩,⟨-3266087581260,-3265045945377⟩⟩⟩
noncomputable def centerBoxes84 := centerStep83.proposed :: centerBoxes83
theorem centerAccepted83 : StepValid centerStep83.shape centerBoxes83 centerStep83.proposed := by
  dsimp only [StepValid,centerStep83]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨457631473861,457631587202⟩,⟨1758492453713,1758495269342⟩,⟨205269694758,205271767373⟩,⟨-31065188110803,-31065103560661⟩,⟨1088715299495,1088802345665⟩,⟨-294458083911,-294364173959⟩⟩⟩
noncomputable def centerBoxes85 := centerStep84.proposed :: centerBoxes84
theorem centerAccepted84 : StepValid centerStep84.shape centerBoxes84 centerStep84.proposed := by
  dsimp only [StepValid,centerStep84]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep85 : Instruction 40 := ⟨.mul 88 85,⟨⟨220331822284,220331822286⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes86 := centerStep85.proposed :: centerBoxes85
theorem centerAccepted85 : StepValid centerStep85.shape centerBoxes85 centerStep85.proposed := by
  dsimp only [StepValid,centerStep85]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep86 : Instruction 40 := ⟨.neg 0,⟨⟨-220331822286,-220331822284⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes87 := centerStep86.proposed :: centerBoxes86
theorem centerAccepted86 : StepValid centerStep86.shape centerBoxes86 centerStep86.proposed := by
  dsimp only [StepValid,centerStep86]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep87 : Instruction 40 := ⟨.add 89 0,⟨⟨879179805490,879179805492⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes88 := centerStep87.proposed :: centerBoxes87
theorem centerAccepted87 : StepValid centerStep87.shape centerBoxes87 centerStep87.proposed := by
  dsimp only [StepValid,centerStep87]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep88 : Instruction 40 := ⟨.mul 12 0,⟨⟨1929849185432,1929849231699⟩,⟨-14578718540443,-14578718424289⟩,⟨0,0⟩,⟨135272188302591,135272188335022⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes89 := centerStep88.proposed :: centerBoxes88
theorem centerAccepted88 : StepValid centerStep88.shape centerBoxes88 centerStep88.proposed := by
  dsimp only [StepValid,centerStep88]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep89 : Instruction 40 := ⟨.neg 91,⟨⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes90 := centerStep89.proposed :: centerBoxes89
theorem centerAccepted89 : StepValid centerStep89.shape centerBoxes89 centerStep89.proposed := by
  dsimp only [StepValid,centerStep89]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep90 : Instruction 40 := ⟨.add 1 0,⟨⟨830337557656,830337603923⟩,⟨-14578718540443,-14578718424289⟩,⟨0,0⟩,⟨135272188302591,135272188335022⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes91 := centerStep90.proposed :: centerBoxes90
theorem centerAccepted90 : StepValid centerStep90.shape centerBoxes90 centerStep90.proposed := by
  dsimp only [StepValid,centerStep90]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨33780830796,33780832681⟩,⟨-677602995522,-677602986047⟩,⟨331972847757,331972866257⟩,⟨8470309304169,8470309329526⟩,⟨-6658977614141,-6658977521421⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes92 := centerStep91.proposed :: centerBoxes91
theorem centerAccepted91 : StepValid centerStep91.shape centerBoxes91 centerStep91.proposed := by
  dsimp only [StepValid,centerStep91]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨491412304657,491412419883⟩,⟨1080889458191,1080892283295⟩,⟨537242542515,537244633630⟩,⟨-22594878806634,-22594794231135⟩,⟨-5570262314646,-5570175175756⟩,⟨-294458083911,-294364173959⟩⟩⟩
noncomputable def centerBoxes93 := centerStep92.proposed :: centerBoxes92
theorem centerAccepted92 : StepValid centerStep92.shape centerBoxes92 centerStep92.proposed := by
  dsimp only [StepValid,centerStep92]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep93 : Instruction 40 := ⟨.inv 17,⟨⟨500903595558,500903607567⟩,⟨2531120470889,2531120592376⟩,⟨0,0⟩,⟨3131155626176,3131158552760⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes94 := centerStep93.proposed :: centerBoxes93
theorem centerAccepted93 : StepValid centerStep93.shape centerBoxes93 centerStep93.proposed := by
  dsimp only [StepValid,centerStep93]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨223872293922,223872351783⟩,⟨1623671014360,1623672632750⟩,⟨244751137172,244752095688⟩,⟨-3917598437960,-3917544779181⟩,⟨-1300885643386,-1300841011560⟩,⟨-134146027002,-134103241307⟩⟩⟩
noncomputable def centerBoxes95 := centerStep94.proposed :: centerBoxes94
theorem centerAccepted94 : StepValid centerStep94.shape centerBoxes94 centerStep94.proposed := by
  dsimp only [StepValid,centerStep94]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-674564814998,-674563654464⟩,⟨5159017791112,5159037871168⟩,⟨-5908865592394,-5908842603488⟩,⟨-68960442010636,-68959888338268⟩,⟨36561703744080,36562465347130⟩,⟨11882281776962,11883323409972⟩⟩⟩
noncomputable def centerBoxes96 := centerStep95.proposed :: centerBoxes95
theorem centerAccepted95 : StepValid centerStep95.shape centerBoxes95 centerStep95.proposed := by
  dsimp only [StepValid,centerStep95]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3726855364138,3726856621184⟩,⟨-15196678815405,-15196658734421⟩,⟨-9540885661517,-9540862672426⟩,⟨82701448670234,82702002394334⟩,⟨65006554906456,65007316516291⟩,⟨20499517605674,20500559241557⟩⟩⟩
noncomputable def centerBoxes97 := centerStep96.proposed :: centerBoxes96
theorem centerAccepted96 : StepValid centerStep96.shape centerBoxes96 centerStep96.proposed := by
  dsimp only [StepValid,centerStep96]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨451067988589,451068140743⟩,⟨565121995927,565125237423⟩,⟨-84558389310,-84555245885⟩,⟨-15612900659370,-15612805701509⟩,⟨-8004907298340,-8004792715325⟩,⟨-4189798066224,-4189658390196⟩⟩⟩
noncomputable def centerBoxes98 := centerStep97.proposed :: centerBoxes97
theorem centerAccepted97 : StepValid centerStep97.shape centerBoxes97 centerStep97.proposed := by
  dsimp only [StepValid,centerStep97]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨309795236084,309795236088⟩,⟨1975255459430,1975255459432⟩,⟨879179805490,879179805492⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes99 := centerStep98.proposed :: centerBoxes98
theorem centerAccepted98 : StepValid centerStep98.shape centerBoxes98 centerStep98.proposed := by
  dsimp only [StepValid,centerStep98]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-309795236088,-309795236084⟩,⟨-1975255459432,-1975255459430⟩,⟨-879179805492,-879179805490⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes100 := centerStep99.proposed :: centerBoxes99
theorem centerAccepted99 : StepValid centerStep99.shape centerBoxes99 centerStep99.proposed := by
  dsimp only [StepValid,centerStep99]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨789716391688,789716391692⟩,⟨-1975255459432,-1975255459430⟩,⟨-879179805492,-879179805490⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes101 := centerStep100.proposed :: centerBoxes100
theorem centerAccepted100 : StepValid centerStep100.shape centerBoxes100 centerStep100.proposed := by
  dsimp only [StepValid,centerStep100]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1427816725910,1427816753683⟩,⟨-9432196756219,-9432196686449⟩,⟨-4198240217435,-4198240186374⟩,⟨60560267720299,60560267732027⟩,⟨37455906731424,37455906814392⟩,⟨11997662823400,11997662825806⟩⟩⟩
noncomputable def centerBoxes102 := centerStep101.proposed :: centerBoxes101
theorem centerAccepted101 : StepValid centerStep101.shape centerBoxes101 centerStep101.proposed := by
  dsimp only [StepValid,centerStep101]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1427816753683,-1427816725910⟩,⟨9432196686449,9432196756219⟩,⟨4198240186374,4198240217435⟩,⟨-60560267732027,-60560267720299⟩,⟨-37455906814392,-37455906731424⟩,⟨-11997662825806,-11997662823400⟩⟩⟩
noncomputable def centerBoxes103 := centerStep102.proposed :: centerBoxes102
theorem centerAccepted102 : StepValid centerStep102.shape centerBoxes102 centerStep102.proposed := by
  dsimp only [StepValid,centerStep102]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-328305125907,-328305098134⟩,⟨9432196686449,9432196756219⟩,⟨4198240186374,4198240217435⟩,⟨-60560267732027,-60560267720299⟩,⟨-37455906814392,-37455906731424⟩,⟨-11997662825806,-11997662823400⟩⟩⟩
noncomputable def centerBoxes104 := centerStep103.proposed :: centerBoxes103
theorem centerAccepted103 : StepValid centerStep103.shape centerBoxes103 centerStep103.proposed := by
  dsimp only [StepValid,centerStep103]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-13356519655,-13356518523⟩,⟨417140028479,417140034171⟩,⟨39540128581,39540140963⟩,⟨-4383387956136,-4383387941275⟩,⟨2148309768954,2148309831276⟩,⟨2868848290220,2868848315198⟩⟩⟩
noncomputable def centerBoxes105 := centerStep104.proposed :: centerBoxes104
theorem centerAccepted104 : StepValid centerStep104.shape centerBoxes104 centerStep104.proposed := by
  dsimp only [StepValid,centerStep104]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨437711468934,437711622220⟩,⟨982262024406,982265271594⟩,⟨-45018260729,-45015104922⟩,⟨-19996288615506,-19996193642784⟩,⟨-5856597529386,-5856482884049⟩,⟨-1320949776004,-1320810074998⟩⟩⟩
noncomputable def centerBoxes106 := centerStep105.proposed :: centerBoxes105
theorem centerAccepted105 : StepValid centerStep105.shape centerBoxes105 centerStep105.proposed := by
  dsimp only [StepValid,centerStep105]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-99127803250,-99127803248⟩,⟨-879179805492,-879179805490⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes107 := centerStep106.proposed :: centerBoxes106
theorem centerAccepted106 : StepValid centerStep106.shape centerBoxes106 centerStep106.proposed := by
  dsimp only [StepValid,centerStep106]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4032841243,4032841245⟩,⟨25680863779,25680863783⟩,⟨39631760400,39631760401⟩,⟨-268390241407,-268390241398⟩,⟨252372404139,252372404144⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes108 := centerStep107.proposed :: centerBoxes107
theorem centerAccepted107 : StepValid centerStep107.shape centerBoxes107 centerStep107.proposed := by
  dsimp only [StepValid,centerStep107]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨8852313644,8852313861⟩,⟨11639235338,11639236724⟩,⟨86993946002,86993948090⟩,⟨-762096333931,-762096319337⟩,⟨114381737068,114381750391⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes109 := centerStep108.proposed :: centerBoxes108
theorem centerAccepted108 : StepValid centerStep108.shape centerBoxes108 centerStep108.proposed := by
  dsimp only [StepValid,centerStep108]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1501927494425,1501927515869⟩,⟨-7835341113578,-7835340715239⟩,⟨-1483021079169,-1483021007224⟩,⟨118184876377041,118184884564378⟩,⟨25270294248698,25270295919239⟩,⟨5638237777051,5638238096969⟩⟩⟩
noncomputable def centerBoxes110 := centerStep109.proposed :: centerBoxes109
theorem centerAccepted109 : StepValid centerStep109.shape centerBoxes109 centerStep109.proposed := by
  dsimp only [StepValid,centerStep109]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨12092217049,12092217519⟩,⟨-47184231497,-47184224621⟩,⟨106893304557,106893309980⟩,⟨-255384875415,-255384723183⟩,⟨-275936004238,-275935916340⟩,⟨-189280643422,-189280622713⟩⟩⟩
noncomputable def centerBoxes111 := centerStep110.proposed :: centerBoxes110
theorem centerAccepted110 : StepValid centerStep110.shape centerBoxes110 centerStep110.proposed := by
  dsimp only [StepValid,centerStep110]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-12092217519,-12092217049⟩,⟨47184224621,47184231497⟩,⟨-106893309980,-106893304557⟩,⟨255384723183,255384875415⟩,⟨275935916340,275936004238⟩,⟨189280622713,189280643422⟩⟩⟩
noncomputable def centerBoxes112 := centerStep111.proposed :: centerBoxes111
theorem centerAccepted111 : StepValid centerStep111.shape centerBoxes111 centerStep111.proposed := by
  dsimp only [StepValid,centerStep111]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-111220020769,-111220020297⟩,⟨-831995580871,-831995573993⟩,⟨-106893309980,-106893304557⟩,⟨2454407978735,2454408130967⟩,⟨275935916340,275936004238⟩,⟨189280622713,189280643422⟩⟩⟩
noncomputable def centerBoxes113 := centerStep112.proposed :: centerBoxes112
theorem centerAccepted112 : StepValid centerStep112.shape centerBoxes112 centerStep112.proposed := by
  dsimp only [StepValid,centerStep112]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨80875463598,80875465177⟩,⟨-534265547956,-534265543980⟩,⟨647021444523,647021459998⟩,⟨3430300008879,3430300009668⟩,⟨-3723548505714,-3723548466510⟩,⟨-2553620134264,-2553620133968⟩⟩⟩
noncomputable def centerBoxes114 := centerStep113.proposed :: centerBoxes113
theorem centerAccepted113 : StepValid centerStep113.shape centerBoxes113 centerStep113.proposed := by
  dsimp only [StepValid,centerStep113]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨110475486874,110475490609⟩,⟨-1306138969665,-1306138913259⟩,⟨774743309526,774743350707⟩,⟨20993523961549,20993525245265⟩,⟨-7117760120779,-7117759450426⟩,⟨-4818912364807,-4818912156547⟩⟩⟩
noncomputable def centerBoxes115 := centerStep114.proposed :: centerBoxes114
theorem centerAccepted114 : StepValid centerStep114.shape centerBoxes114 centerStep114.proposed := by
  dsimp only [StepValid,centerStep114]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-110475490609,-110475486874⟩,⟨1306138913259,1306138969665⟩,⟨-774743350707,-774743309526⟩,⟨-20993525245265,-20993523961549⟩,⟨7117759450426,7117760120779⟩,⟨4818912156547,4818912364807⟩⟩⟩
noncomputable def centerBoxes116 := centerStep115.proposed :: centerBoxes115
theorem centerAccepted115 : StepValid centerStep115.shape centerBoxes115 centerStep115.proposed := by
  dsimp only [StepValid,centerStep115]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨989036137167,989036140902⟩,⟨1306138913259,1306138969665⟩,⟨-774743350707,-774743309526⟩,⟨-20993525245265,-20993523961549⟩,⟨7117759450426,7117760120779⟩,⟨4818912156547,4818912364807⟩⟩⟩
noncomputable def centerBoxes117 := centerStep116.proposed :: centerBoxes116
theorem centerAccepted116 : StepValid centerStep116.shape centerBoxes116 centerStep116.proposed := by
  dsimp only [StepValid,centerStep116]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨119704817452,119704817907⟩,⟨796166983127,796166992375⟩,⟨190239942144,190239948210⟩,⟨-2451543081809,-2451542847550⟩,⟨-684024730379,-684024601074⟩,⟨-177886734001,-177886683924⟩⟩⟩
noncomputable def centerBoxes118 := centerStep117.proposed :: centerBoxes117
theorem centerAccepted117 : StepValid centerStep117.shape centerBoxes117 centerStep117.proposed := by
  dsimp only [StepValid,centerStep117]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11250352067,11250352164⟩,⟨168319392516,168319394624⟩,⟨21625374760,21625375952⟩,⟨762588227810,762588281538⟩,⟨105947307306,105947334876⟩,⟨-17508898116,-17508891653⟩⟩⟩
noncomputable def centerBoxes119 := centerStep118.proposed :: centerBoxes118
theorem centerAccepted118 : StepValid centerStep118.shape centerBoxes118 centerStep118.proposed := by
  dsimp only [StepValid,centerStep118]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨168116042828,168116189576⟩,⟨1673455581098,1673460935750⟩,⟨116757028711,116759909876⟩,⟨-1666235503867,-1666024241896⟩,⟨433082471195,433231129553⟩,⟨-608341958850,-608217620341⟩⟩⟩
noncomputable def centerBoxes120 := centerStep119.proposed :: centerBoxes119
theorem centerAccepted119 : StepValid centerStep119.shape centerBoxes119 centerStep119.proposed := by
  dsimp only [StepValid,centerStep119]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-168116189576,-168116042828⟩,⟨-1673460935750,-1673455581098⟩,⟨-116759909876,-116757028711⟩,⟨1666024241896,1666235503867⟩,⟨-433231129553,-433082471195⟩,⟨608217620341,608341958850⟩⟩⟩
noncomputable def centerBoxes121 := centerStep120.proposed :: centerBoxes120
theorem centerAccepted120 : StepValid centerStep120.shape centerBoxes120 centerStep120.proposed := by
  dsimp only [StepValid,centerStep120]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨55756104346,55756308955⟩,⟨-49789921390,-49782948348⟩,⟨127991227296,127995066977⟩,⟨-2251574196064,-2251309275314⟩,⟨-1734116772939,-1733923482755⟩,⟨474071593339,474238717543⟩⟩⟩
noncomputable def centerBoxes122 := centerStep121.proposed :: centerBoxes121
theorem centerAccepted121 : StepValid centerStep121.shape centerBoxes121 centerStep121.proposed := by
  dsimp only [StepValid,centerStep121]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨29706000542297,29706026793941⟩,⟨-270677987273787,-270677323788948⟩,⟨-90743821557682,-90743317650775⟩,⟨4013770487900931,4013794410107997⟩,⟨1474829257118324,1474850555579423⟩,⟨340972779175777,340994710318345⟩⟩⟩
noncomputable def centerBoxes123 := centerStep122.proposed :: centerBoxes122
theorem centerAccepted122 : StepValid centerStep122.shape centerBoxes122 centerStep122.proposed := by
  dsimp only [StepValid,centerStep122]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13032370881,13032370981⟩,⟨173358827626,173358830300⟩,⟨41423186386,41423187868⟩,⟨619221003620,619221083447⟩,⟨126568384096,126568424808⟩,⟨27098097205,27098112459⟩⟩⟩
noncomputable def centerBoxes124 := centerStep123.proposed :: centerBoxes123
theorem centerAccepted123 : StepValid centerStep123.shape centerBoxes123 centerStep123.proposed := by
  dsimp only [StepValid,centerStep123]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨352101430015,352101743875⟩,⟨1475401842005,1475413942140⟩,⟨43573937065,43580947114⟩,⟨-21050539930557,-21050028539091⟩,⟨-3604532620792,-3604170884632⟩,⟨-2063768013321,-2063468762992⟩⟩⟩
noncomputable def centerBoxes125 := centerStep124.proposed :: centerBoxes124
theorem centerAccepted124 : StepValid centerStep124.shape centerBoxes124 centerStep124.proposed := by
  dsimp only [StepValid,centerStep124]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-352101743875,-352101430015⟩,⟨-1475413942140,-1475401842005⟩,⟨-43580947114,-43573937065⟩,⟨21050028539091,21050539930557⟩,⟨3604170884632,3604532620792⟩,⟨2063468762992,2063768013321⟩⟩⟩
noncomputable def centerBoxes126 := centerStep125.proposed :: centerBoxes125
theorem centerAccepted125 : StepValid centerStep125.shape centerBoxes125 centerStep125.proposed := by
  dsimp only [StepValid,centerStep125]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨85609725059,85610192205⟩,⟨-493151917734,-493136570411⟩,⟨-88599207843,-88589041987⟩,⟨1053739923585,1054346287773⟩,⟨-2252426644754,-2251950263257⟩,⟨742518986988,742957938323⟩⟩⟩
noncomputable def centerBoxes127 := centerStep126.proposed :: centerBoxes126
theorem centerAccepted126 : StepValid centerStep126.shape centerBoxes126 centerStep126.proposed := by
  dsimp only [StepValid,centerStep126]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨232203667459,232203667464⟩,⟨1588536384663,1588536384672⟩,⟨315732315191,315732315196⟩,⟨-3973281040305,-3973281040301⟩,⟨-1579432783384,-1579432783376⟩,⟨-351500207392,-351500207389⟩⟩⟩
noncomputable def centerBoxes128 := centerStep127.proposed :: centerBoxes127
theorem centerAccepted127 : StepValid centerStep127.shape centerBoxes127 centerStep127.proposed := by
  dsimp only [StepValid,centerStep127]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1661982293852,-1661980850398⟩,⟨-4111020896818,-4110978951431⟩,⟨443048927861,443075926301⟩,⟨41299484693428,41301034540908⟩,⟨-7769443905165,-7768208710794⟩,⟨2332703871179,2333883311861⟩⟩⟩
noncomputable def centerBoxes129 := centerStep128.proposed :: centerBoxes128
theorem centerAccepted128 : StepValid centerStep128.shape centerBoxes128 centerStep128.proposed := by
  dsimp only [StepValid,centerStep128]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-180941504232,-180941346393⟩,⟨-1651027971223,-1651022343690⟩,⟨-239324740030,-239321541581⟩,⟨2248312972937,2248546111109⟩,⟨-202402183231,-202239776121⟩,⟨676165071214,676303135724⟩⟩⟩
noncomputable def centerBoxes130 := centerStep129.proposed :: centerBoxes129
theorem centerAccepted129 : StepValid centerStep129.shape centerBoxes129 centerStep129.proposed := by
  dsimp only [StepValid,centerStep129]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨51262163227,51262321071⟩,⟨-62491586560,-62485959018⟩,⟨76407575161,76410773615⟩,⟨-1724968067368,-1724734929192⟩,⟨-1781834966615,-1781672559497⟩,⟨324664863822,324802928335⟩⟩⟩
noncomputable def centerBoxes131 := centerStep130.proposed :: centerBoxes130
theorem centerAccepted130 : StepValid centerStep130.shape centerBoxes130 centerStep130.proposed := by
  dsimp only [StepValid,centerStep130]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨4341259012,4341298633⟩,⟨-28884510746,-28883076626⟩,⟨5472728819,5473614163⟩,⟨-77221267684,-77161094196⟩,⟨-302639687271,-302594793327⟩,⟨53937202934,53975799978⟩⟩⟩
noncomputable def centerBoxes132 := centerStep131.proposed :: centerBoxes131
theorem centerAccepted131 : StepValid centerStep131.shape centerBoxes131 centerStep131.proposed := by
  dsimp only [StepValid,centerStep131]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨2389978707,2389993426⟩,⟨-5827066662,-5826523976⟩,⟨7124649690,7124969872⟩,⟨-153743479738,-153719966096⟩,⟨-174834033948,-174817232930⟩,⟨40892956867,40906813088⟩⟩⟩
noncomputable def centerBoxes133 := centerStep132.proposed :: centerBoxes132
theorem centerAccepted132 : StepValid centerStep132.shape centerBoxes132 centerStep132.proposed := by
  dsimp only [StepValid,centerStep132]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨4321110221,4321136918⟩,⟨-28272836416,-28271745788⟩,⟨4986579775,4987207543⟩,⟨-96938301849,-96887146041⟩,⟨-287903704617,-287868772320⟩,⟨45594141176,45621425513⟩⟩⟩
noncomputable def centerBoxes134 := centerStep133.proposed :: centerBoxes133
theorem centerAccepted133 : StepValid centerStep133.shape centerBoxes133 centerStep133.proposed := by
  dsimp only [StepValid,centerStep133]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-4321136918,-4321110221⟩,⟨28271745788,28272836416⟩,⟨-4987207543,-4986579775⟩,⟨96887146041,96938301849⟩,⟨287868772320,287903704617⟩,⟨-45621425513,-45594141176⟩⟩⟩
noncomputable def centerBoxes135 := centerStep134.proposed :: centerBoxes134
theorem centerAccepted134 : StepValid centerStep134.shape centerBoxes134 centerStep134.proposed := by
  dsimp only [StepValid,centerStep134]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨20122094,20188412⟩,⟨-612764958,-610240210⟩,⟨485521276,487034388⟩,⟨19665878357,19777207653⟩,⟨-14770914951,-14691088710⟩,⟨8315777421,8381658802⟩⟩⟩
noncomputable def centerBoxes136 := centerStep135.proposed :: centerBoxes135
theorem centerAccepted135 : StepValid centerStep135.shape centerBoxes135 centerStep135.proposed := by
  dsimp only [StepValid,centerStep135]
  exact ⟨by decide,by decide⟩
noncomputable def centerProgram : List (Instruction 40) := [centerStep0,centerStep1,centerStep2,centerStep3,centerStep4,centerStep5,centerStep6,centerStep7,centerStep8,centerStep9,centerStep10,centerStep11,centerStep12,centerStep13,centerStep14,centerStep15,centerStep16,centerStep17,centerStep18,centerStep19,centerStep20,centerStep21,centerStep22,centerStep23,centerStep24,centerStep25,centerStep26,centerStep27,centerStep28,centerStep29,centerStep30,centerStep31,centerStep32,centerStep33,centerStep34,centerStep35,centerStep36,centerStep37,centerStep38,centerStep39,centerStep40,centerStep41,centerStep42,centerStep43,centerStep44,centerStep45,centerStep46,centerStep47,centerStep48,centerStep49,centerStep50,centerStep51,centerStep52,centerStep53,centerStep54,centerStep55,centerStep56,centerStep57,centerStep58,centerStep59,centerStep60,centerStep61,centerStep62,centerStep63,centerStep64,centerStep65,centerStep66,centerStep67,centerStep68,centerStep69,centerStep70,centerStep71,centerStep72,centerStep73,centerStep74,centerStep75,centerStep76,centerStep77,centerStep78,centerStep79,centerStep80,centerStep81,centerStep82,centerStep83,centerStep84,centerStep85,centerStep86,centerStep87,centerStep88,centerStep89,centerStep90,centerStep91,centerStep92,centerStep93,centerStep94,centerStep95,centerStep96,centerStep97,centerStep98,centerStep99,centerStep100,centerStep101,centerStep102,centerStep103,centerStep104,centerStep105,centerStep106,centerStep107,centerStep108,centerStep109,centerStep110,centerStep111,centerStep112,centerStep113,centerStep114,centerStep115,centerStep116,centerStep117,centerStep118,centerStep119,centerStep120,centerStep121,centerStep122,centerStep123,centerStep124,centerStep125,centerStep126,centerStep127,centerStep128,centerStep129,centerStep130,centerStep131,centerStep132,centerStep133,centerStep134,centerStep135]
theorem centerAccepted : Accepted centerProgram centerInitial :=
  ⟨centerAccepted0,⟨centerAccepted1,⟨centerAccepted2,⟨centerAccepted3,⟨centerAccepted4,⟨centerAccepted5,⟨centerAccepted6,⟨centerAccepted7,⟨centerAccepted8,⟨centerAccepted9,⟨centerAccepted10,⟨centerAccepted11,⟨centerAccepted12,⟨centerAccepted13,⟨centerAccepted14,⟨centerAccepted15,⟨centerAccepted16,⟨centerAccepted17,⟨centerAccepted18,⟨centerAccepted19,⟨centerAccepted20,⟨centerAccepted21,⟨centerAccepted22,⟨centerAccepted23,⟨centerAccepted24,⟨centerAccepted25,⟨centerAccepted26,⟨centerAccepted27,⟨centerAccepted28,⟨centerAccepted29,⟨centerAccepted30,⟨centerAccepted31,⟨centerAccepted32,⟨centerAccepted33,⟨centerAccepted34,⟨centerAccepted35,⟨centerAccepted36,⟨centerAccepted37,⟨centerAccepted38,⟨centerAccepted39,⟨centerAccepted40,⟨centerAccepted41,⟨centerAccepted42,⟨centerAccepted43,⟨centerAccepted44,⟨centerAccepted45,⟨centerAccepted46,⟨centerAccepted47,⟨centerAccepted48,⟨centerAccepted49,⟨centerAccepted50,⟨centerAccepted51,⟨centerAccepted52,⟨centerAccepted53,⟨centerAccepted54,⟨centerAccepted55,⟨centerAccepted56,⟨centerAccepted57,⟨centerAccepted58,⟨centerAccepted59,⟨centerAccepted60,⟨centerAccepted61,⟨centerAccepted62,⟨centerAccepted63,⟨centerAccepted64,⟨centerAccepted65,⟨centerAccepted66,⟨centerAccepted67,⟨centerAccepted68,⟨centerAccepted69,⟨centerAccepted70,⟨centerAccepted71,⟨centerAccepted72,⟨centerAccepted73,⟨centerAccepted74,⟨centerAccepted75,⟨centerAccepted76,⟨centerAccepted77,⟨centerAccepted78,⟨centerAccepted79,⟨centerAccepted80,⟨centerAccepted81,⟨centerAccepted82,⟨centerAccepted83,⟨centerAccepted84,⟨centerAccepted85,⟨centerAccepted86,⟨centerAccepted87,⟨centerAccepted88,⟨centerAccepted89,⟨centerAccepted90,⟨centerAccepted91,⟨centerAccepted92,⟨centerAccepted93,⟨centerAccepted94,⟨centerAccepted95,⟨centerAccepted96,⟨centerAccepted97,⟨centerAccepted98,⟨centerAccepted99,⟨centerAccepted100,⟨centerAccepted101,⟨centerAccepted102,⟨centerAccepted103,⟨centerAccepted104,⟨centerAccepted105,⟨centerAccepted106,⟨centerAccepted107,⟨centerAccepted108,⟨centerAccepted109,⟨centerAccepted110,⟨centerAccepted111,⟨centerAccepted112,⟨centerAccepted113,⟨centerAccepted114,⟨centerAccepted115,⟨centerAccepted116,⟨centerAccepted117,⟨centerAccepted118,⟨centerAccepted119,⟨centerAccepted120,⟨centerAccepted121,⟨centerAccepted122,⟨centerAccepted123,⟨centerAccepted124,⟨centerAccepted125,⟨centerAccepted126,⟨centerAccepted127,⟨centerAccepted128,⟨centerAccepted129,⟨centerAccepted130,⟨centerAccepted131,⟨centerAccepted132,⟨centerAccepted133,⟨centerAccepted134,⟨centerAccepted135,True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
noncomputable def center_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨55756104346,55756308955⟩,⟨-49789921390,-49782948348⟩,⟨127991227296,127995066977⟩,⟨-2251574196064,-2251309275314⟩,⟨-1734116772939,-1733923482755⟩,⟨474071593339,474238717543⟩⟩
theorem center_m11_eq : (finalBoxes centerProgram centerInitial).getD 14 (zeroBox 40)=center_m11 := rfl
noncomputable def center_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨20122094,20188412⟩,⟨-612764958,-610240210⟩,⟨485521276,487034388⟩,⟨19665878357,19777207653⟩,⟨-14770914951,-14691088710⟩,⟨8315777421,8381658802⟩⟩
theorem center_kdet_eq : (finalBoxes centerProgram centerInitial).getD 0 (zeroBox 40)=center_kdet := rfl
noncomputable def wholeInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨109951162777,110380659508⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨109951162777,113816633344⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
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
noncomputable def wholeStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-110380659508,-109951162777⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes3 := wholeStep2.proposed :: wholeBoxes2
theorem wholeAccepted2 : StepValid wholeStep2.shape wholeBoxes2 wholeStep2.proposed := by
  dsimp only [StepValid,wholeStep2]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨439375154380,439804651111⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes4 := wholeStep3.proposed :: wholeBoxes3
theorem wholeAccepted3 : StepValid wholeStep3.shape wholeBoxes3 wholeStep3.proposed := by
  dsimp only [StepValid,wholeStep3]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨43937515437,45526653338⟩,⟨-113816633344,-109951162777⟩,⟨439375154380,439804651111⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes5 := wholeStep4.proposed :: wholeBoxes4
theorem wholeAccepted4 : StepValid wholeStep4.shape wholeBoxes4 wholeStep4.proposed := by
  dsimp only [StepValid,wholeStep4]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨153888678214,155907312846⟩,⟨985694994432,989560464999⟩,⟨439375154380,439804651111⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes6 := wholeStep5.proposed :: wholeBoxes5
theorem wholeAccepted5 : StepValid wholeStep5.shape wholeBoxes5 wholeStep5.proposed := by
  dsimp only [StepValid,wholeStep5]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨43508018706,45956150069⟩,⟨-113816633344,-109951162777⟩,⟨439375154380,439804651111⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes7 := wholeStep6.proposed :: wholeBoxes6
theorem wholeAccepted6 : StepValid wholeStep6.shape wholeBoxes6 wholeStep6.proposed := by
  dsimp only [StepValid,wholeStep6]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep7 : Instruction 40 := ⟨.log 7,⟨⟨-2531719137984,-2527432479680⟩,⟨10952333724070,10995116277821⟩,⟨0,0⟩,⟨-109951162778821,-109097176394608⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes8 := wholeStep7.proposed :: wholeBoxes7
theorem wholeAccepted7 : StepValid wholeStep7.shape wholeBoxes7 wholeStep7.proposed := by
  dsimp only [StepValid,wholeStep7]
  exact ⟨by decide,by decide,lc19,by decide⟩
noncomputable def wholeStep8 : Instruction 40 := ⟨.mul 8 0,⟨⟨-254160866589,-252743247966⟩,⟨-1436485765583,-1423625884593⟩,⟨0,0⟩,⟨10866601497217,11080514916241⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes9 := wholeStep8.proposed :: wholeBoxes8
theorem wholeAccepted8 : StepValid wholeStep8.shape wholeBoxes8 wholeStep8.proposed := by
  dsimp only [StepValid,wholeStep8]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep9 : Instruction 40 := ⟨.neg 0,⟨⟨252743247966,254160866589⟩,⟨1423625884593,1436485765583⟩,⟨0,0⟩,⟨-11080514916241,-10866601497217⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes10 := wholeStep9.proposed :: wholeBoxes9
theorem wholeAccepted9 : StepValid wholeStep9.shape wholeBoxes9 wholeStep9.proposed := by
  dsimp only [StepValid,wholeStep9]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep10 : Instruction 40 := ⟨.add 12 7,⟨⟨989130968268,989560464999⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes11 := wholeStep10.proposed :: wholeBoxes10
theorem wholeAccepted10 : StepValid wholeStep10.shape wholeBoxes10 wholeStep10.proposed := by
  dsimp only [StepValid,wholeStep10]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep11 : Instruction 40 := ⟨.log 0,⟨⟨-116322434304,-115845112064⟩,⟨-1222210059535,-1221679586417⟩,⟨0,0⟩,⟨-1358600847770,-1357421762684⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes12 := wholeStep11.proposed :: wholeBoxes11
theorem wholeAccepted11 : StepValid wholeStep11.shape wholeBoxes11 wholeStep11.proposed := by
  dsimp only [StepValid,wholeStep11]
  exact ⟨by decide,by decide,lc20,by decide⟩
noncomputable def wholeStep12 : Instruction 40 := ⟨.mul 1 0,⟨⟨-104690190874,-104215348860⟩,⟨-984143941519,-982711974881⟩,⟨0,0⟩,⟨1220618409840,1223270775532⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes13 := wholeStep12.proposed :: wholeBoxes12
theorem wholeAccepted12 : StepValid wholeStep12.shape wholeBoxes12 wholeStep12.proposed := by
  dsimp only [StepValid,wholeStep12]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep13 : Instruction 40 := ⟨.neg 0,⟨⟨104215348860,104690190874⟩,⟨982711974881,984143941519⟩,⟨0,0⟩,⟨-1223270775532,-1220618409840⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes14 := wholeStep13.proposed :: wholeBoxes13
theorem wholeAccepted13 : StepValid wholeStep13.shape wholeBoxes13 wholeStep13.proposed := by
  dsimp only [StepValid,wholeStep13]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep14 : Instruction 40 := ⟨.add 4 0,⟨⟨356958596826,358851057463⟩,⟨2406337859474,2420629707102⟩,⟨0,0⟩,⟨-12303785691773,-12087219907057⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes15 := wholeStep14.proposed :: wholeBoxes14
theorem wholeAccepted14 : StepValid wholeStep14.shape wholeBoxes14 wholeStep14.proposed := by
  dsimp only [StepValid,wholeStep14]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2162070810560,-2147741704512⟩,⟨6951457811918,7070261765073⟩,⟨3098623678248,3142338562257⟩,⟨-45464368146570,-43949299389058⟩,⟨-28062232248567,-27344603604983⟩,⟨-8980615930201,-8732484911342⟩⟩⟩
noncomputable def wholeBoxes16 := wholeStep15.proposed :: wholeBoxes15
theorem wholeAccepted15 : StepValid wholeStep15.shape wholeBoxes15 wholeStep15.proposed := by
  dsimp only [StepValid,wholeStep15]
  exact ⟨by decide,by decide,lc21,by decide⟩
noncomputable def wholeStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-306574884469,-300599942468⟩,⟨-972931177169,-922875855902⟩,⟨-431142049264,-412683931875⟩,⟨6017041296629,6575286032247⟩,⟨3724340289218,3991103866551⟩,⟨1203054868357,1291664074928⟩⟩⟩
noncomputable def wholeBoxes17 := wholeStep16.proposed :: wholeBoxes16
theorem wholeAccepted16 : StepValid wholeStep16.shape wholeBoxes16 wholeStep16.proposed := by
  dsimp only [StepValid,wholeStep16]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep17 : Instruction 40 := ⟨.neg 0,⟨⟨300599942468,306574884469⟩,⟨922875855902,972931177169⟩,⟨412683931875,431142049264⟩,⟨-6575286032247,-6017041296629⟩,⟨-3991103866551,-3724340289218⟩,⟨-1291664074928,-1203054868357⟩⟩⟩
noncomputable def wholeBoxes18 := wholeStep17.proposed :: wholeBoxes17
theorem wholeAccepted17 : StepValid wholeStep17.shape wholeBoxes17 wholeStep17.proposed := by
  dsimp only [StepValid,wholeStep17]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-155907312846,-153888678214⟩,⟨-989560464999,-985694994432⟩,⟨-439804651111,-439375154380⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes19 := wholeStep18.proposed :: wholeBoxes18
theorem wholeAccepted18 : StepValid wholeStep18.shape wholeBoxes18 wholeStep18.proposed := by
  dsimp only [StepValid,wholeStep18]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨943604314930,945622949562⟩,⟨-989560464999,-985694994432⟩,⟨-439804651111,-439375154380⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes20 := wholeStep19.proposed :: wholeBoxes19
theorem wholeAccepted19 : StepValid wholeStep19.shape wholeBoxes19 wholeStep19.proposed := by
  dsimp only [StepValid,wholeStep19]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep20 : Instruction 40 := ⟨.log 0,⟨⟨-168131232448,-165781580608⟩,⟨-1153060896860,-1146104912449⟩,⟨-512471509716,-510878137443⟩,⟨-1209218164030,-1194672650254⟩,⟨741013528784,748651488359⟩,⟨-238857908945,-237374907844⟩⟩⟩
noncomputable def wholeBoxes21 := wholeStep20.proposed :: wholeBoxes20
theorem wholeAccepted20 : StepValid wholeStep20.shape wholeBoxes20 wholeStep20.proposed := by
  dsimp only [StepValid,wholeStep20]
  exact ⟨by decide,by decide,lc22,by decide⟩
noncomputable def wholeStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-144599427532,-142274270545⟩,⟨-843056816066,-832272708236⟩,⟨-374497642962,-371184721067⟩,⟨1014955436089,1050237812552⟩,⟨1383797429113,1400536661071⟩,⟨202876254327,206261320066⟩⟩⟩
noncomputable def wholeBoxes22 := wholeStep21.proposed :: wholeBoxes21
theorem wholeAccepted21 : StepValid wholeStep21.shape wholeBoxes21 wholeStep21.proposed := by
  dsimp only [StepValid,wholeStep21]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep22 : Instruction 40 := ⟨.neg 0,⟨⟨142274270545,144599427532⟩,⟨832272708236,843056816066⟩,⟨371184721067,374497642962⟩,⟨-1050237812552,-1014955436089⟩,⟨-1400536661071,-1383797429113⟩,⟨-206261320066,-202876254327⟩⟩⟩
noncomputable def wholeBoxes23 := wholeStep22.proposed :: wholeBoxes22
theorem wholeAccepted22 : StepValid wholeStep22.shape wholeBoxes22 wholeStep22.proposed := by
  dsimp only [StepValid,wholeStep22]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨442874213013,451174312001⟩,⟨1755148564138,1815987993235⟩,⟨783868652942,805639692226⟩,⟨-7625523844799,-7031996732718⟩,⟨-5391640527622,-5108137718331⟩,⟨-1497925394994,-1405931122684⟩⟩⟩
noncomputable def wholeBoxes24 := wholeStep23.proposed :: wholeBoxes23
theorem wholeAccepted23 : StepValid wholeStep23.shape wholeBoxes23 wholeStep23.proposed := by
  dsimp only [StepValid,wholeStep23]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨799832809839,810025369464⟩,⟨4161486423612,4236617700337⟩,⟨783868652942,805639692226⟩,⟨-19929309536572,-19119216639775⟩,⟨-5391640527622,-5108137718331⟩,⟨-1497925394994,-1405931122684⟩⟩⟩
noncomputable def wholeBoxes25 := wholeStep24.proposed :: wholeBoxes24
theorem wholeAccepted24 : StepValid wholeStep24.shape wholeBoxes24 wholeStep24.proposed := by
  dsimp only [StepValid,wholeStep24]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨87016037412,91912300138⟩,⟨-227633266688,-219902325554⟩,⟨878750308760,879609302222⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes26 := wholeStep25.proposed :: wholeBoxes25
theorem wholeAccepted25 : StepValid wholeStep25.shape wholeBoxes25 wholeStep25.proposed := by
  dsimp only [StepValid,wholeStep25]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep26 : Instruction 40 := ⟨.inv 0,⟨⟨13153036294375,13893138041792⟩,⟨31468946646819,36344339400640⟩,⟨-140440013382287,-125752861014895⟩,⟨150580380209832,190153009708169⟩,⟨-420090465384546,-250633282776086⟩,⟨2404582744167513,2839300566867880⟩⟩⟩
noncomputable def wholeBoxes27 := wholeStep26.proposed :: wholeBoxes26
theorem wholeAccepted26 : StepValid wholeStep26.shape wholeBoxes26 wholeStep26.proposed := by
  dsimp only [StepValid,wholeStep26]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨9568093425736,10235266268244⟩,⟨72674154569099,80308156149850⟩,⟨-94086973045113,-81298276850060⟩,⟨95927742779961,191455141961513⟩,⟨-896319639893420,-692753587866541⟩,⟨1524463359741161,1895628680429354⟩⟩⟩
noncomputable def wholeBoxes28 := wholeStep27.proposed :: wholeBoxes27
theorem wholeAccepted27 : StepValid wholeStep27.shape wholeBoxes27 wholeStep27.proposed := by
  dsimp only [StepValid,wholeStep27]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep28 : Instruction 40 := ⟨.contact 0,⟨⟨81545019392,87181409536⟩,⟨-725534104695,-574087925350⟩,⟨642213994344,850017121852⟩,⟨6308680755337,11278981482093⟩,⟨-8629567481109,-894568398912⟩,⟨-7066469165091,4479028035702⟩⟩⟩
noncomputable def wholeBoxes29 := wholeStep28.proposed :: wholeBoxes28
theorem wholeAccepted28 : StepValid wholeStep28.shape wholeBoxes28 wholeStep28.proposed := by
  dsimp only [StepValid,wholeStep28]
  exact ⟨by decide,by decide,(⟨⟨81545019392,87181409536⟩,⟨-9933401820,-8685568522⟩,⟨1839954362,2256264278⟩⟩ : DyadicJetEnclosure 40),brwhole28_jet,by decide⟩
noncomputable def wholeStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes30 := wholeStep29.proposed :: wholeBoxes29
theorem wholeAccepted29 : StepValid wholeStep29.shape wholeBoxes29 wholeStep29.proposed := by
  dsimp only [StepValid,wholeStep29]
  exact ⟨by decide,by decide,lc4,by decide⟩
noncomputable def wholeStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1181056647168,1186693037312⟩,⟨-725534104695,-574087925350⟩,⟨642213994344,850017121852⟩,⟨6308680755337,11278981482093⟩,⟨-8629567481109,-894568398912⟩,⟨-7066469165091,4479028035702⟩⟩⟩
noncomputable def wholeBoxes31 := wholeStep30.proposed :: wholeBoxes30
theorem wholeAccepted30 : StepValid wholeStep30.shape wholeBoxes30 wholeStep30.proposed := by
  dsimp only [StepValid,wholeStep30]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep31 : Instruction 40 := ⟨.log 0,⟨⟨78662794688,83897544192⟩,⟨-675440239360,-531912069458⟩,⟨595033199066,791328435878⟩,⟨5430278944446,10242910362215⟩,⟨-7745886639908,-342727740870⟩,⟨-7148097217940,3847757682873⟩⟩⟩
noncomputable def wholeBoxes32 := wholeStep31.proposed :: wholeBoxes31
theorem wholeAccepted31 : StepValid wholeStep31.shape wholeBoxes31 wholeStep31.proposed := by
  dsimp only [StepValid,wholeStep31]
  exact ⟨by decide,by decide,lc32,by decide⟩
noncomputable def wholeStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨84496802220,90549866891⟩,⟨-784358015863,-612433401280⟩,⟨685109864775,918933705297⟩,⟨6839813154483,12807121597385⟩,⟨-10062886575708,-1053515803826⟩,⟨-7558973550240,5718149753286⟩⟩⟩
noncomputable def wholeBoxes33 := wholeStep32.proposed :: wholeBoxes32
theorem wholeAccepted32 : StepValid wholeStep32.shape wholeBoxes32 wholeStep32.proposed := by
  dsimp only [StepValid,wholeStep32]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-87181409536,-81545019392⟩,⟨574087925350,725534104695⟩,⟨-850017121852,-642213994344⟩,⟨-11278981482093,-6308680755337⟩,⟨894568398912,8629567481109⟩,⟨-4479028035702,7066469165091⟩⟩⟩
noncomputable def wholeBoxes34 := wholeStep33.proposed :: wholeBoxes33
theorem wholeAccepted33 : StepValid wholeStep33.shape wholeBoxes33 wholeStep33.proposed := by
  dsimp only [StepValid,wholeStep33]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1012330218240,1017966608384⟩,⟨574087925350,725534104695⟩,⟨-850017121852,-642213994344⟩,⟨-11278981482093,-6308680755337⟩,⟨894568398912,8629567481109⟩,⟨-4479028035702,7066469165091⟩⟩⟩
noncomputable def wholeBoxes35 := wholeStep34.proposed :: wholeBoxes34
theorem wholeAccepted34 : StepValid wholeStep34.shape wholeBoxes34 wholeStep34.proposed := by
  dsimp only [StepValid,wholeStep34]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep35 : Instruction 40 := ⟨.log 0,⟨⟨-90832069824,-84727255552⟩,⟨620075692158,788016765763⟩,⟨-923220202703,-693659053730⟩,⟨-12815091453287,-7163737743482⟩,⟨1357421385062,10034411053173⟩,⟨-5639954515886,7237415124155⟩⟩⟩
noncomputable def wholeBoxes36 := wholeStep35.proposed :: wholeBoxes35
theorem wholeAccepted35 : StepValid wholeStep35.shape wholeBoxes35 wholeStep35.proposed := by
  dsimp only [StepValid,wholeStep35]
  exact ⟨by decide,by decide,lc33,by decide⟩
noncomputable def wholeStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-84095530885,-78009144184⟩,⟨510971946195,685335053307⟩,⟨-805261433306,-568437105069⟩,⟨-10731002513184,-4623970091854⟩,⟨-681519191333,8496916495892⟩,⟨-4995119786484,8498129567454⟩⟩⟩
noncomputable def wholeBoxes37 := wholeStep36.proposed :: wholeBoxes36
theorem wholeAccepted36 : StepValid wholeStep36.shape wholeBoxes36 wholeStep36.proposed := by
  dsimp only [StepValid,wholeStep36]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨401271335,12540722707⟩,⟨-273386069668,72901652027⟩,⟨-120151568531,350496600228⟩,⟨-3891189358701,8183151505531⟩,⟨-10744405767041,7443400692066⟩,⟨-12554093336724,14216279320740⟩⟩⟩
noncomputable def wholeBoxes38 := wholeStep37.proposed :: wholeBoxes37
theorem wholeAccepted37 : StepValid wholeStep37.shape wholeBoxes37 wholeStep37.proposed := by
  dsimp only [StepValid,wholeStep37]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨200635667,6270361354⟩,⟨-136693034834,36450826014⟩,⟨-60075784266,175248300114⟩,⟨-1945594679351,4091575752766⟩,⟨-5372202883521,3721700346033⟩,⟨-6277046668362,7108139660370⟩⟩⟩
noncomputable def wholeBoxes39 := wholeStep38.proposed :: wholeBoxes38
theorem wholeAccepted38 : StepValid wholeStep38.shape wholeBoxes38 wholeStep38.proposed := by
  dsimp only [StepValid,wholeStep38]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-6270361354,-200635667⟩,⟨-36450826014,136693034834⟩,⟨-175248300114,60075784266⟩,⟨-4091575752766,1945594679351⟩,⟨-3721700346033,5372202883521⟩,⟨-7108139660370,6277046668362⟩⟩⟩
noncomputable def wholeBoxes40 := wholeStep39.proposed :: wholeBoxes39
theorem wholeAccepted39 : StepValid wholeStep39.shape wholeBoxes39 wholeStep39.proposed := by
  dsimp only [StepValid,wholeStep39]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨755853022262,761922767213⟩,⟨-36450826014,136693034834⟩,⟨-175248300114,60075784266⟩,⟨-4091575752766,1945594679351⟩,⟨-3721700346033,5372202883521⟩,⟨-7108139660370,6277046668362⟩⟩⟩
noncomputable def wholeBoxes41 := wholeStep40.proposed :: wholeBoxes40
theorem wholeAccepted40 : StepValid wholeStep40.shape wholeBoxes40 wholeStep40.proposed := by
  dsimp only [StepValid,wholeStep40]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨6047767044,6912703765⟩,⟨-115056693020,-85154189956⟩,⟨95259297490,134797466332⟩,⟨1535260599782,2746159663394⟩,⟨-2490295206676,-803329198022⟩,⟨-370393404819,2024566283482⟩⟩⟩
noncomputable def wholeBoxes42 := wholeStep41.proposed :: wholeBoxes41
theorem wholeAccepted41 : StepValid wholeStep41.shape wholeBoxes41 wholeStep41.proposed := by
  dsimp only [StepValid,wholeStep41]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-6912703765,-6047767044⟩,⟨85154189956,115056693020⟩,⟨-134797466332,-95259297490⟩,⟨-2746159663394,-1535260599782⟩,⟨803329198022,2490295206676⟩,⟨-2024566283482,370393404819⟩⟩⟩
noncomputable def wholeBoxes43 := wholeStep42.proposed :: wholeBoxes42
theorem wholeAccepted42 : StepValid wholeStep42.shape wholeBoxes42 wholeStep42.proposed := by
  dsimp only [StepValid,wholeStep42]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1092598924011,1093463860732⟩,⟨85154189956,115056693020⟩,⟨-134797466332,-95259297490⟩,⟨-2746159663394,-1535260599782⟩,⟨803329198022,2490295206676⟩,⟨-2024566283482,370393404819⟩⟩⟩
noncomputable def wholeBoxes44 := wholeStep43.proposed :: wholeBoxes43
theorem wholeAccepted43 : StepValid wholeStep43.shape wholeBoxes43 wholeStep43.proposed := by
  dsimp only [StepValid,wholeStep43]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep44 : Instruction 40 := ⟨.log 0,⟨⟨-6934525632,-6064460864⟩,⟨85625163640,115784638855⟩,⟨-135650308975,-95786160846⟩,⟨-2775726950334,-1550419985018⟩,⟨815231686299,2520335643555⟩,⟨-2054111017803,364392222859⟩⟩⟩
noncomputable def wholeBoxes45 := wholeStep44.proposed :: wholeBoxes44
theorem wholeAccepted44 : StepValid wholeStep44.shape wholeBoxes44 wholeStep44.proposed := by
  dsimp only [StepValid,wholeStep44]
  exact ⟨by decide,by decide,lc30,by decide⟩
noncomputable def wholeStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-3467262816,-3032230432⟩,⟨42812581820,57892319428⟩,⟨-67825154488,-47893080423⟩,⟨-1387863475167,-775209992509⟩,⟨407615843149,1260167821778⟩,⟨-1027055508902,182196111430⟩⟩⟩
noncomputable def wholeBoxes46 := wholeStep45.proposed :: wholeBoxes45
theorem wholeAccepted45 : StepValid wholeStep45.shape wholeBoxes45 wholeStep45.proposed := by
  dsimp only [StepValid,wholeStep45]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3032230432,3467262816⟩,⟨-57892319428,-42812581820⟩,⟨47893080423,67825154488⟩,⟨775209992509,1387863475167⟩,⟨-1260167821778,-407615843149⟩,⟨-182196111430,1027055508902⟩⟩⟩
noncomputable def wholeBoxes47 := wholeStep46.proposed :: wholeBoxes46
theorem wholeAccepted46 : StepValid wholeStep46.shape wholeBoxes46 wholeStep46.proposed := by
  dsimp only [StepValid,wholeStep46]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765155614048,765590665696⟩,⟨-57892319428,-42812581820⟩,⟨47893080423,67825154488⟩,⟨775209992509,1387863475167⟩,⟨-1260167821778,-407615843149⟩,⟨-182196111430,1027055508902⟩⟩⟩
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
noncomputable def wholeStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨273149731002,273365965183⟩,⟨21288547489,28764173255⟩,⟨-33699366583,-23814824372⟩,⟨-686539915849,-383815149945⟩,⟨200832299505,622573801669⟩,⟨-506141570871,92598351205⟩⟩⟩
noncomputable def wholeBoxes51 := wholeStep50.proposed :: wholeBoxes50
theorem wholeAccepted50 : StepValid wholeStep50.shape wholeBoxes50 wholeStep50.proposed := by
  dsimp only [StepValid,wholeStep50]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1530311228096,1531181331392⟩,⟨-115784638856,-85625163640⟩,⟨95786160846,135650308976⟩,⟨1550419985018,2775726950334⟩,⟨-2520335643556,-815231686298⟩,⟨-364392222860,2054111017804⟩⟩⟩
noncomputable def wholeBoxes52 := wholeStep51.proposed :: wholeBoxes51
theorem wholeAccepted51 : StepValid wholeStep51.shape wholeBoxes51 wholeStep51.proposed := by
  dsimp only [StepValid,wholeStep51]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1187588875369,1194201059924⟩,⟨-855880404662,-669747345358⟩,⟨749225160243,1002727498973⟩,⟨8115302352020,14532128175148⟩,⟨-11617221749565,-1888688389870⟩,⟨-7390659073691,6967618851972⟩⟩⟩
noncomputable def wholeBoxes53 := wholeStep52.proposed :: wholeBoxes52
theorem wholeAccepted52 : StepValid wholeStep52.shape wholeBoxes52 wholeStep52.proposed := by
  dsimp only [StepValid,wholeStep52]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1275666122962,1288890492072⟩,⟨-1711760809325,-1339494690716⟩,⟨1498450320485,2005454997946⟩,⟨16230604704044,29064256350283⟩,⟨-23234443499121,-3777376779740⟩,⟨-14776472076050,13935237703938⟩⟩⟩
noncomputable def wholeBoxes54 := wholeStep53.proposed :: wholeBoxes53
theorem wholeAccepted53 : StepValid wholeStep53.shape wholeBoxes53 wholeStep53.proposed := by
  dsimp only [StepValid,wholeStep53]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep54 : Instruction 40 := ⟨.log 0,⟨⟨163390050304,174729614016⟩,⟨-1475386764568,-1142680465753⟩,⟨1278280475456,1728525238332⟩,⟨11866057209149,23863280028790⟩,⟨-18697571884471,-902927675768⟩,⟨-15453402805473,10524829967535⟩⟩⟩
noncomputable def wholeBoxes55 := wholeStep54.proposed :: wholeBoxes54
theorem wholeAccepted54 : StepValid wholeStep54.shape wholeBoxes54 wholeStep54.proposed := by
  dsimp only [StepValid,wholeStep54]
  exact ⟨by decide,by decide,lc35,by decide⟩
noncomputable def wholeStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨56057660329,60413641044⟩,⟨-505659761210,-383814951391⟩,⟨427590743802,593795347606⟩,⟨3832042381658,8018310021315⟩,⟨-6342905065746,32318012320⟩,⟨-5731389580258,3694409408244⟩⟩⟩
noncomputable def wholeBoxes56 := wholeStep55.proposed :: wholeBoxes55
theorem wholeAccepted55 : StepValid wholeStep55.shape wholeBoxes55 wholeStep55.proposed := by
  dsimp only [StepValid,wholeStep55]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380172514545,380689800774⟩,⟨842668393,18785317194⟩,⟨-23133795298,580334481⟩,⟨-576966339743,152601362666⟩,⟨-343388607165,671567981674⟩,⟨-803765592579,635506372840⟩⟩⟩
noncomputable def wholeBoxes57 := wholeStep56.proposed :: wholeBoxes56
theorem wholeAccepted56 : StepValid wholeStep56.shape wholeBoxes56 wholeStep56.proposed := by
  dsimp only [StepValid,wholeStep56]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3175619144922,3179940088677⟩,⟨-157129147791,-7029329065⟩,⟨-4854188061,193501845234⟩,⟨-1276397796985,4841543680592⟩,⟨-5636430442224,2872742060671⟩,⟨-5316262238497,6746619483963⟩⟩⟩
noncomputable def wholeBoxes58 := wholeStep57.proposed :: wholeBoxes57
theorem wholeAccepted57 : StepValid wholeStep57.shape wholeBoxes57 wholeStep57.proposed := by
  dsimp only [StepValid,wholeStep57]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨161906227149,174724627013⟩,⟨-1471071745833,-1108896099581⟩,⟨1234704625889,1727970612903⟩,⟨11002513234593,23600613109868⟩,⟨-18828108328792,250812301750⟩,⟨-16873323181458,11264446056823⟩⟩⟩
noncomputable def wholeBoxes59 := wholeStep58.proposed :: wholeBoxes58
theorem wholeAccepted58 : StepValid wholeStep58.shape wholeBoxes58 wholeStep58.proposed := by
  dsimp only [StepValid,wholeStep58]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨325296277453,349454241029⟩,⟨-2946458510401,-2251576565334⟩,⟨2512985101345,3456495851235⟩,⟨22868570443742,47463893138658⟩,⟨-37525680213263,-652115374018⟩,⟨-32326725986931,21789276024358⟩⟩⟩
noncomputable def wholeBoxes60 := wholeStep59.proposed :: wholeBoxes59
theorem wholeAccepted59 : StepValid wholeStep59.shape wholeBoxes59 wholeStep59.proposed := by
  dsimp only [StepValid,wholeStep59]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨519606866203,527985596998⟩,⟨-50518272882,189446901204⟩,⟨-242881778418,83260798040⟩,⟨-5679698540626,2730444735313⟩,⟨-5201588370946,7460431567442⟩,⟨-9870530664261,8755408515167⟩⟩⟩
noncomputable def wholeBoxes61 := wholeStep60.proposed :: wholeBoxes60
theorem wholeAccepted60 : StepValid wholeStep60.shape wholeBoxes60 wholeStep60.proposed := by
  dsimp only [StepValid,wholeStep60]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨357200788319,365875391357⟩,⟨-52511071230,196920028255⟩,⟨-252462755341,86545193394⟩,⟨-5913166830912,2873481317217⟩,⟨-5452069016736,7770250479965⟩,⟨-10279800359373,9158852257433⟩⟩⟩
noncomputable def wholeBoxes62 := wholeStep61.proposed :: wholeBoxes61
theorem wholeAccepted61 : StepValid wholeStep61.shape wholeBoxes61 wholeStep61.proposed := by
  dsimp only [StepValid,wholeStep61]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨714401576638,731750782714⟩,⟨-105022142460,393840056510⟩,⟨-504925510682,173090386788⟩,⟨-11826333661824,5746962634434⟩,⟨-10904138033472,15540500959930⟩,⟨-20559600718746,18317704514866⟩⟩⟩
noncomputable def wholeBoxes63 := wholeStep62.proposed :: wholeBoxes62
theorem wholeAccepted62 : StepValid wholeStep62.shape wholeBoxes62 wholeStep62.proposed := by
  dsimp only [StepValid,wholeStep62]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1523398524331,1525133564348⟩,⟨-30630448900,29431529380⟩,⟨-39011305486,40391011486⟩,⟨-1195739678376,1240466350552⟩,⟨-1717006445534,1675063520378⟩,⟨-2388958506342,2424504422623⟩⟩⟩
noncomputable def wholeBoxes64 := wholeStep63.proposed :: wholeBoxes63
theorem wholeAccepted63 : StepValid wholeStep63.shape wholeBoxes63 wholeStep63.proposed := by
  dsimp only [StepValid,wholeStep63]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨989819734632,1015012166550⟩,⟨-166061590266,565883268637⟩,⟨-726345567420,266974996363⟩,⟨-17222054204333,8818260958074⟩,⟨-16295337136705,22699571087474⟩,⟨-30145245806893,27057899017628⟩⟩⟩
noncomputable def wholeBoxes65 := wholeStep64.proposed :: wholeBoxes64
theorem wholeAccepted64 : StepValid wholeStep64.shape wholeBoxes64 wholeStep64.proposed := by
  dsimp only [StepValid,wholeStep64]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67858105054,67965584932⟩,⟨10577352476,14302979226⟩,⟨-16757003090,-11832549482⟩,⟨-340557461602,-189196047902⟩,⟨98021617606,308652497864⟩,⟨-250647159521,48110241478⟩⟩⟩
noncomputable def wholeBoxes66 := wholeStep65.proposed :: wholeBoxes65
theorem wholeAccepted65 : StepValid wholeStep65.shape wholeBoxes65 wholeStep65.proposed := by
  dsimp only [StepValid,wholeStep65]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨49362951209,50071183110⟩,⟨264527167442,272420926349⟩,⟨36032582811,41192571760⟩,⟨-1402743097196,-1207378325472⟩,⟨-319002408314,-122172549295⟩,⟨-301805036794,-68197218696⟩⟩⟩
noncomputable def wholeBoxes67 := wholeStep66.proposed :: wholeBoxes66
theorem wholeAccepted66 : StepValid wholeStep66.shape wholeBoxes66 wholeStep66.proposed := by
  dsimp only [StepValid,wholeStep66]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2129902400007,2132325125425⟩,⟨-322483679118,-238347910136⟩,⟨266632264244,377813595518⟩,⟨4329116163689,7755347487526⟩,⟨-7048214880872,-2284213967390⟩,⟨-998216965562,5754586617321⟩⟩⟩
noncomputable def wholeBoxes68 := wholeStep67.proposed :: wholeBoxes67
theorem wholeAccepted67 : StepValid wholeStep67.shape wholeBoxes67 wholeStep67.proposed := by
  dsimp only [StepValid,wholeStep67]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2964419361414,2969478759505⟩,⟨-673636790194,-497602490769⟩,⟨556652159155,789215561149⟩,⟨9065802694521,16251099551958⟩,⟨-14782708680210,-4799933839777⟩,⟨-2050341675170,12090685408050⟩⟩⟩
noncomputable def wholeBoxes69 := wholeStep68.proposed :: wholeBoxes68
theorem wholeAccepted68 : StepValid wholeStep68.shape wholeBoxes68 wholeStep68.proposed := by
  dsimp only [StepValid,wholeStep68]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨133088622806,135228505959⟩,⟨682520899966,713394026176⟩,⟨122139389985,147190279465⟩,⟨-3715219075186,-2754607210559⟩,⟨-1426049313357,-365653831248⟩,⟨-871979363806,425870352747⟩⟩⟩
noncomputable def wholeBoxes70 := wholeStep69.proposed :: wholeBoxes69
theorem wholeAccepted69 : StepValid wholeStep69.shape wholeBoxes69 wholeStep69.proposed := by
  dsimp only [StepValid,wholeStep69]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8939874111906,9083615068862⟩,⟨-48690839153508,-45121040724139⟩,⟨-10046086677802,-8074560632222⟩,⟨637572290868670,775566876885967⟩,⟨105680469495795,205031195764249⟩,⟨-14480658389619,81735743226773⟩⟩⟩
noncomputable def wholeBoxes71 := wholeStep70.proposed :: wholeBoxes70
theorem wholeAccepted70 : StepValid wholeStep70.shape wholeBoxes70 wholeStep70.proposed := by
  dsimp only [StepValid,wholeStep70]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨8047994761991,8385522788696⟩,⟨-46320777713882,-35944531891508⟩,⟨-15274730454260,-5063394712381⟩,⟨381566189610907,803522980727210⟩,⟨-56479716174376,410489491089419⟩,⟨-267291362815466,312266069269874⟩⟩⟩
noncomputable def wholeBoxes72 := wholeStep71.proposed :: wholeBoxes71
theorem wholeAccepted71 : StepValid wholeStep71.shape wholeBoxes71 wholeStep71.proposed := by
  dsimp only [StepValid,wholeStep71]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨16095989523982,16771045577392⟩,⟨-92641555427764,-71889063783016⟩,⟨-30549460908520,-10126789424762⟩,⟨763132379221814,1607045961454420⟩,⟨-112959432348752,820978982178838⟩,⟨-534582725630932,624532138539748⟩⟩⟩
noncomputable def wholeBoxes73 := wholeStep72.proposed :: wholeBoxes72
theorem wholeAccepted72 : StepValid wholeStep72.shape wholeBoxes72 wholeStep72.proposed := by
  dsimp only [StepValid,wholeStep72]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10952333724070,10995116277821⟩,⟨-109951162778821,-109097176394608⟩,⟨0,0⟩,⟨2173453475238562,2199023255588622⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes74 := wholeStep73.proposed :: wholeBoxes73
theorem wholeAccepted73 : StepValid wholeStep73.shape wholeBoxes73 wholeStep73.proposed := by
  dsimp only [StepValid,wholeStep73]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9852822096294,9895604650045⟩,⟨-109951162778820,-109097176394608⟩,⟨0,0⟩,⟨2173453475238575,2199023255588602⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes75 := wholeStep74.proposed :: wholeBoxes74
theorem wholeAccepted74 : StepValid wholeStep74.shape wholeBoxes74 wholeStep74.proposed := by
  dsimp only [StepValid,wholeStep74]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep75 : Instruction 40 := ⟨.log 0,⟨⟨2411110045440,2415874025920⟩,⟨-12269843176037,-12121908488212⟩,⟨0,0⟩,⟨104571265817406,111755106875729⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes76 := wholeStep75.proposed :: wholeBoxes75
theorem wholeAccepted75 : StepValid wholeStep75.shape wholeBoxes75 wholeStep75.proposed := by
  dsimp only [StepValid,wholeStep75]
  exact ⟨by decide,by decide,lc36,by decide⟩
noncomputable def wholeStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7754131589765,7855846405631⟩,⟨-50515964607269,-49024055091935⟩,⟨-22451539825470,-21852552661855⟩,⟨619890944546097,649672243686862⟩,⟨331002186189480,344872068980200⟩,⟨123168933183822,128330319740810⟩⟩⟩
noncomputable def wholeBoxes77 := wholeStep76.proposed :: wholeBoxes76
theorem wholeAccepted76 : StepValid wholeStep76.shape wholeBoxes76 wholeStep76.proposed := by
  dsimp only [StepValid,wholeStep76]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6654619961989,6756334777855⟩,⟨-50515964607269,-49024055091935⟩,⟨-22451539825470,-21852552661855⟩,⟨619890944546102,649672243686854⟩,⟨331002186189482,344872068980197⟩,⟨123168933183822,128330319740809⟩⟩⟩
noncomputable def wholeBoxes78 := wholeStep77.proposed :: wholeBoxes77
theorem wholeAccepted77 : StepValid wholeStep77.shape wholeBoxes77 wholeStep77.proposed := by
  dsimp only [StepValid,wholeStep77]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep78 : Instruction 40 := ⟨.log 0,⟨⟨1979610472128,1996289228864⟩,⟨-8346515772704,-7978071008387⟩,⟨-3709562565650,-3556238188046⟩,⟨37520405863500,49453306623816⟩,⟨25706891060807,31177481920930⟩,⟨7528827410441,9701191582639⟩⟩⟩
noncomputable def wholeBoxes79 := wholeStep78.proposed :: wholeBoxes78
theorem wholeAccepted78 : StepValid wholeStep78.shape wholeBoxes78 wholeStep78.proposed := by
  dsimp only [StepValid,wholeStep78]
  exact ⟨by decide,by decide,lc37,by decide⟩
noncomputable def wholeStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨98913096826,99342593558⟩,⟨878750308760,879609302222⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes80 := wholeStep79.proposed :: wholeBoxes79
theorem wholeAccepted79 : StepValid wholeStep79.shape wholeBoxes79 wholeStep79.proposed := by
  dsimp only [StepValid,wholeStep79]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨132067744545,134086379178⟩,⟨705609942955,713101859099⟩,⟨314710205396,316753821306⟩,⟨-1781208837000,-1767320322048⟩,⟨-1583382643350,-1575482923412⟩,⟨-351843720890,-351156861664⟩⟩⟩
noncomputable def wholeBoxes81 := wholeStep80.proposed :: wholeBoxes80
theorem wholeAccepted80 : StepValid wholeStep80.shape wholeBoxes80 wholeStep80.proposed := by
  dsimp only [StepValid,wholeStep80]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4390720517568,4412163254784⟩,⟨-20616358948741,-20099979496599⟩,⟨-3709562565650,-3556238188046⟩,⟨142091671680906,161208413499545⟩,⟨25706891060807,31177481920930⟩,⟨7528827410441,9701191582639⟩⟩⟩
noncomputable def wholeBoxes82 := wholeStep81.proposed :: wholeBoxes81
theorem wholeAccepted81 : StepValid wholeStep81.shape wholeBoxes81 wholeStep81.proposed := by
  dsimp only [StepValid,wholeStep81]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨650592554906,698908482058⟩,⟨-5892917020802,-4503153130668⟩,⟨5025970202690,6912991702470⟩,⟨45737140887484,94927786277316⟩,⟨-75051360426526,-1304230748036⟩,⟨-64653451973862,43578552048716⟩⟩⟩
noncomputable def wholeBoxes83 := wholeStep82.proposed :: wholeBoxes82
theorem wholeAccepted82 : StepValid wholeStep82.shape wholeBoxes82 wholeStep82.proposed := by
  dsimp only [StepValid,wholeStep82]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5041313072474,5111071736842⟩,⟨-26509275969543,-24603132627267⟩,⟨1316407637040,3356753514424⟩,⟨187828812568390,256136199776861⟩,⟨-49344469365719,29873251172894⟩,⟨-57124624563421,53279743631355⟩⟩⟩
noncomputable def wholeBoxes84 := wholeStep83.proposed :: wholeBoxes83
theorem wholeAccepted83 : StepValid wholeStep83.shape wholeBoxes83 wholeStep83.proposed := by
  dsimp only [StepValid,wholeStep83]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨453521250226,461793317481⟩,⟨1633957427504,1875536512914⟩,⟨118425265159,303287924961⟩,⟨-35739728956998,-26266890090767⟩,⟨-3406252241832,5384497732011⟩,⟨-5161299086610,4813908086767⟩⟩⟩
noncomputable def wholeBoxes85 := wholeStep84.proposed :: wholeBoxes84
theorem wholeAccepted84 : StepValid wholeStep84.shape wholeBoxes84 wholeStep84.proposed := by
  dsimp only [StepValid,wholeStep84]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep85 : Instruction 40 := ⟨.mul 88 85,⟨⟨219902325554,220761319016⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes86 := wholeStep85.proposed :: wholeBoxes85
theorem wholeAccepted85 : StepValid wholeStep85.shape wholeBoxes85 wholeStep85.proposed := by
  dsimp only [StepValid,wholeStep85]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep86 : Instruction 40 := ⟨.neg 0,⟨⟨-220761319016,-219902325554⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes87 := wholeStep86.proposed :: wholeBoxes86
theorem wholeAccepted86 : StepValid wholeStep86.shape wholeBoxes86 wholeStep86.proposed := by
  dsimp only [StepValid,wholeStep86]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep87 : Instruction 40 := ⟨.add 89 0,⟨⟨878750308760,879609302222⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes88 := wholeStep87.proposed :: wholeBoxes87
theorem wholeAccepted87 : StepValid wholeStep87.shape wholeBoxes87 wholeStep87.proposed := by
  dsimp only [StepValid,wholeStep87]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep88 : Instruction 40 := ⟨.mul 12 0,⟨⟨1927004356625,1932699220739⟩,⟨-14647622592683,-14510276640425⟩,⟨0,0⟩,⟨132062950305200,138483458204854⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes89 := wholeStep88.proposed :: wholeBoxes88
theorem wholeAccepted88 : StepValid wholeStep88.shape wholeBoxes88 wholeStep88.proposed := by
  dsimp only [StepValid,wholeStep88]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep89 : Instruction 40 := ⟨.neg 91,⟨⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes90 := wholeStep89.proposed :: wholeBoxes89
theorem wholeAccepted89 : StepValid wholeStep89.shape wholeBoxes89 wholeStep89.proposed := by
  dsimp only [StepValid,wholeStep89]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep90 : Instruction 40 := ⟨.add 1 0,⟨⟨827492728849,833187592963⟩,⟨-14647622592683,-14510276640425⟩,⟨0,0⟩,⟨132062950305200,138483458204854⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes91 := wholeStep90.proposed :: wholeBoxes90
theorem wholeAccepted90 : StepValid wholeStep90.shape wholeBoxes90 wholeStep90.proposed := by
  dsimp only [StepValid,wholeStep90]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨32744145870,34824637676⟩,⟨-698472785006,-656925453974⟩,⟨330673852191,333275037186⟩,⟨8127827541019,8820691407275⟩,⟨-6692236630045,-6625935308195⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes92 := wholeStep91.proposed :: wholeBoxes91
theorem wholeAccepted91 : StepValid wholeStep91.shape wholeBoxes91 wholeStep91.proposed := by
  dsimp only [StepValid,wholeStep91]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨486265396096,496617955157⟩,⟨935484642498,1218611058940⟩,⟨449099117350,636562962147⟩,⟨-27611901415979,-17446198683492⟩,⟨-10098488871877,-1241437576184⟩,⟨-5161299086610,4813908086767⟩⟩⟩
noncomputable def wholeBoxes93 := wholeStep92.proposed :: wholeBoxes92
theorem wholeAccepted92 : StepValid wholeStep92.shape wholeBoxes92 wholeStep92.proposed := by
  dsimp only [StepValid,wholeStep92]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep93 : Instruction 40 := ⟨.inv 17,⟨⟨500409295618,501398026980⟩,⟨2510857612204,2551553037358⟩,⟨0,0⟩,⟨1957166706152,4308831445771⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes94 := wholeStep93.proposed :: wholeBoxes93
theorem wholeAccepted93 : StepValid wholeStep93.shape wholeBoxes93 wholeStep93.proposed := by
  dsimp only [StepValid,wholeStep93]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨221308914063,226467148313⟩,⟨1536198744681,1708173142558⟩,⟨204393812033,290284709326⟩,⟨-7453411832207,-338055028904⟩,⟨-3579533275485,912220690666⟩,⟨-2353649668913,2195232825005⟩⟩⟩
noncomputable def wholeBoxes95 := wholeStep94.proposed :: wholeBoxes94
theorem wholeAccepted94 : StepValid wholeStep94.shape wholeBoxes94 wholeStep94.proposed := by
  dsimp only [StepValid,wholeStep94]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-698908482058,-650592554906⟩,⟨4503153130668,5892917020802⟩,⟨-6912991702470,-5025970202690⟩,⟨-94927786277316,-45737140887484⟩,⟨1304230748036,75051360426526⟩,⟨-43578552048716,64653451973862⟩⟩⟩
noncomputable def wholeBoxes96 := wholeStep95.proposed :: wholeBoxes95
theorem wholeAccepted95 : StepValid wholeStep95.shape wholeBoxes95 wholeStep95.proposed := by
  dsimp only [StepValid,wholeStep95]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3691812035510,3761570699878⟩,⟨-16113205818073,-14207062475797⟩,⟨-10622554268120,-8582208390736⟩,⟨47163885403590,115471272612061⟩,⟨27011121808843,106228842347456⟩,⟨-36049724638275,74354643556501⟩⟩⟩
noncomputable def wholeBoxes97 := wholeStep96.proposed :: wholeBoxes96
theorem wholeAccepted96 : StepValid wholeStep96.shape wholeBoxes96 wholeStep96.proposed := by
  dsimp only [StepValid,wholeStep96]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨443441684923,458726749611⟩,⟨404195684205,733133093879⟩,⟨-238732277882,52804341904⟩,⟨-21329496168818,-10087004446287⟩,⟨-13703893761284,-1909343251644⟩,⟨-11720413923706,2975614434509⟩⟩⟩
noncomputable def wholeBoxes98 := wholeStep97.proposed :: wholeBoxes97
theorem wholeAccepted97 : StepValid wholeStep97.shape wholeBoxes97 wholeStep97.proposed := by
  dsimp only [StepValid,wholeStep97]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨307777356428,311814625692⟩,⟨1971389988864,1979120929998⟩,⟨878750308760,879609302222⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes99 := wholeStep98.proposed :: wholeBoxes98
theorem wholeAccepted98 : StepValid wholeStep98.shape wholeBoxes98 wholeStep98.proposed := by
  dsimp only [StepValid,wholeStep98]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-311814625692,-307777356428⟩,⟨-1979120929998,-1971389988864⟩,⟨-879609302222,-878750308760⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes100 := wholeStep99.proposed :: wholeBoxes99
theorem wholeAccepted99 : StepValid wholeStep99.shape wholeBoxes99 wholeStep99.proposed := by
  dsimp only [StepValid,wholeStep99]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨787697002084,791734271348⟩,⟨-1979120929998,-1971389988864⟩,⟨-879609302222,-878750308760⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes101 := wholeStep100.proposed :: wholeBoxes100
theorem wholeAccepted100 : StepValid wholeStep100.shape wholeBoxes100 wholeStep100.proposed := by
  dsimp only [StepValid,wholeStep100]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1418205314793,1437484204885⟩,⟨-9603464039876,-9264919647032⟩,⟨-4268206239949,-4129853071415⟩,⟨55488717269703,65657701090632⟩,⟨35128246245676,39797226418016⟩,⟨11078123490688,12920915950172⟩⟩⟩
noncomputable def wholeBoxes102 := wholeStep101.proposed :: wholeBoxes101
theorem wholeAccepted101 : StepValid wholeStep101.shape wholeBoxes101 wholeStep101.proposed := by
  dsimp only [StepValid,wholeStep101]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1437484204885,-1418205314793⟩,⟨9264919647032,9603464039876⟩,⟨4129853071415,4268206239949⟩,⟨-65657701090632,-55488717269703⟩,⟨-39797226418016,-35128246245676⟩,⟨-12920915950172,-11078123490688⟩⟩⟩
noncomputable def wholeBoxes103 := wholeStep102.proposed :: wholeBoxes102
theorem wholeAccepted102 : StepValid wholeStep102.shape wholeBoxes102 wholeStep102.proposed := by
  dsimp only [StepValid,wholeStep102]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-337972577109,-318693687017⟩,⟨9264919647032,9603464039876⟩,⟨4129853071415,4268206239949⟩,⟨-65657701090632,-55488717269703⟩,⟨-39797226418016,-35128246245676⟩,⟨-12920915950172,-11078123490688⟩⟩⟩
noncomputable def wholeBoxes104 := wholeStep103.proposed :: wholeBoxes103
theorem wholeAccepted103 : StepValid wholeStep103.shape wholeBoxes103 wholeStep103.proposed := by
  dsimp only [StepValid,wholeStep103]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-14126197560,-12610808786⟩,⟨398485134400,436380228611⟩,⟨28230545761,51044697608⟩,⟨-4732503889886,-4048689811857⟩,⟨1915816702021,2376337204487⟩,⟨2760602100537,2976200183549⟩⟩⟩
noncomputable def wholeBoxes105 := wholeStep104.proposed :: wholeBoxes104
theorem wholeAccepted104 : StepValid wholeStep104.shape wholeBoxes104 wholeStep104.proposed := by
  dsimp only [StepValid,wholeStep104]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨429315487363,446115940825⟩,⟨802680818605,1169513322490⟩,⟨-210501732121,103849039512⟩,⟨-26062000058704,-14135694258144⟩,⟨-11788077059263,466993952843⟩,⟨-8959811823169,5951814618058⟩⟩⟩
noncomputable def wholeBoxes106 := wholeStep105.proposed :: wholeBoxes105
theorem wholeAccepted105 : StepValid wholeStep105.shape wholeBoxes105 wholeStep105.proposed := by
  dsimp only [StepValid,wholeStep105]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-99342593558,-98913096826⟩,⟨-879609302222,-878750308760⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes107 := wholeStep106.proposed :: wholeBoxes106
theorem wholeAccepted106 : StepValid wholeStep106.shape wholeBoxes106 wholeStep106.proposed := by
  dsimp only [StepValid,wholeStep106]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨3914022151,4152209966⟩,⟨24488913663,26873610374⟩,⟨39526600801,39737037424⟩,⟨-274018913489,-262766099163⟩,⟨251814268106,252930624064⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes108 := wholeStep107.proposed :: wholeBoxes107
theorem wholeAccepted107 : StepValid wholeStep107.shape wholeBoxes107 wholeStep107.proposed := by
  dsimp only [StepValid,wholeStep107]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨8583027125,9123337993⟩,⟨7365543403,15896001924⟩,⟨86677559241,87311197222⟩,⟨-829614595812,-694155508943⟩,⟨108761645553,119972071186⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes109 := wholeStep108.proposed :: wholeBoxes108
theorem wholeAccepted108 : StepValid wholeStep108.shape wholeBoxes108 wholeStep108.proposed := by
  dsimp only [StepValid,wholeStep108]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1492454267715,1511473153819⟩,⟨-8006090570789,-7667448955409⟩,⟨-1522446630687,-1444261081828⟩,⟨114009424166293,122475728901235⟩,⟨24251348719040,26317210722530⟩,⟨5385645988426,5897683656993⟩⟩⟩
noncomputable def wholeBoxes110 := wholeStep109.proposed :: wholeBoxes109
theorem wholeAccepted109 : StepValid wholeStep109.shape wholeBoxes109 wholeStep109.proposed := by
  dsimp only [StepValid,wholeStep109]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨11650422914,12541641309⟩,⟨-56433722053,-38001910253⟩,⟨105021625145,108750462995⟩,⟨-481962953651,-28701594798⟩,⟨-320824621152,-230828077729⟩,⟨-199750621014,-178773452335⟩⟩⟩
noncomputable def wholeBoxes111 := wholeStep110.proposed :: wholeBoxes110
theorem wholeAccepted110 : StepValid wholeStep110.shape wholeBoxes110 wholeStep110.proposed := by
  dsimp only [StepValid,wholeStep110]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-12541641309,-11650422914⟩,⟨38001910253,56433722053⟩,⟨-108750462995,-105021625145⟩,⟨28701594798,481962953651⟩,⟨230828077729,320824621152⟩,⟨178773452335,199750621014⟩⟩⟩
noncomputable def wholeBoxes112 := wholeStep111.proposed :: wholeBoxes111
theorem wholeAccepted111 : StepValid wholeStep111.shape wholeBoxes111 wholeStep111.proposed := by
  dsimp only [StepValid,wholeStep111]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-111884234867,-110563519740⟩,⟨-841607391969,-822316586707⟩,⟨-108750462995,-105021625145⟩,⟨2227724850350,2680986209203⟩,⟨230828077729,320824621152⟩,⟨178773452335,199750621014⟩⟩⟩
noncomputable def wholeBoxes113 := wholeStep112.proposed :: wholeBoxes112
theorem wholeAccepted112 : StepValid wholeStep112.shape wholeBoxes112 wholeStep112.proposed := by
  dsimp only [StepValid,wholeStep112]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨78333805005,83438651366⟩,⟨-555505403658,-513655810142⟩,⟨636022780641,657794235130⟩,⟨3080308386728,3794983268942⟩,⟨-3962042006528,-3480603439314⟩,⟨-2669731999153,-2436732747400⟩⟩⟩
noncomputable def wholeBoxes114 := wholeStep113.proposed :: wholeBoxes113
theorem wholeAccepted113 : StepValid wholeStep113.shape wholeBoxes113 wholeStep113.proposed := by
  dsimp only [StepValid,wholeStep113]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨106328681418,114701180365⟩,⟨-1371198690661,-1243486856166⟩,⟨747790199683,801359293452⟩,⟨19467616592783,22601014391770⟩,⟨-7833775119123,-6393487421281⟩,⟨-5107961747715,-4530905531360⟩⟩⟩
noncomputable def wholeBoxes115 := wholeStep114.proposed :: wholeBoxes114
theorem wholeAccepted114 : StepValid wholeStep114.shape wholeBoxes114 wholeStep114.proposed := by
  dsimp only [StepValid,wholeStep114]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-114701180365,-106328681418⟩,⟨1243486856166,1371198690661⟩,⟨-801359293452,-747790199683⟩,⟨-22601014391770,-19467616592783⟩,⟨6393487421281,7833775119123⟩,⟨4530905531360,5107961747715⟩⟩⟩
noncomputable def wholeBoxes116 := wholeStep115.proposed :: wholeBoxes115
theorem wholeAccepted115 : StepValid wholeStep115.shape wholeBoxes115 wholeStep115.proposed := by
  dsimp only [StepValid,wholeStep115]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨984810447411,993182946358⟩,⟨1243486856166,1371198690661⟩,⟨-801359293452,-747790199683⟩,⟨-22601014391770,-19467616592783⟩,⟨6393487421281,7833775119123⟩,⟨4530905531360,5107961747715⟩⟩⟩
noncomputable def wholeBoxes117 := wholeStep116.proposed :: wholeBoxes116
theorem wholeAccepted116 : StepValid wholeStep116.shape wholeBoxes116 wholeStep116.proposed := by
  dsimp only [StepValid,wholeStep116]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨118290422136,121119505947⟩,⟨781361948687,811359926082⟩,⟨184153152168,196301269580⟩,⟨-2769157660683,-2142688627955⟩,⟨-826119479359,-540663019616⟩,⟨-235309877080,-119679739315⟩⟩⟩
noncomputable def wholeBoxes118 := wholeStep117.proposed :: wholeBoxes117
theorem wholeAccepted117 : StepValid wholeStep117.shape wholeBoxes117 wholeStep117.proposed := by
  dsimp only [StepValid,wholeStep117]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11117928713,11385129267⟩,⟨165379271796,171280769990⟩,⟨21121305552,22132485072⟩,⟨684384718746,840369287745⟩,⟨91796768274,120060628996⟩,⟨-20589875293,-14441245954⟩⟩⟩
noncomputable def wholeBoxes119 := wholeStep118.proposed :: wholeBoxes118
theorem wholeAccepted118 : StepValid wholeStep118.shape wholeBoxes118 wholeStep118.proposed := by
  dsimp only [StepValid,wholeStep118]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨162757773153,173659392969⟩,⟨1461746198647,1885655468550⟩,⟨-7131574042,235191685505⟩,⟨-11127788856720,7832909976714⟩,⟨-6449609780692,7428154436488⟩,⟨-7079395934140,5866378121647⟩⟩⟩
noncomputable def wholeBoxes120 := wholeStep119.proposed :: wholeBoxes119
theorem wholeAccepted119 : StepValid wholeStep119.shape wholeBoxes119 wholeStep119.proposed := by
  dsimp only [StepValid,wholeStep119]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-173659392969,-162757773153⟩,⟨-1885655468550,-1461746198647⟩,⟨-235191685505,7131574042⟩,⟨-7832909976714,11127788856720⟩,⟨-7428154436488,6449609780692⟩,⟨-5866378121647,7079395934140⟩⟩⟩
noncomputable def wholeBoxes121 := wholeStep120.proposed :: wholeBoxes120
theorem wholeAccepted120 : StepValid wholeStep120.shape wholeBoxes120 wholeStep120.proposed := by
  dsimp only [StepValid,wholeStep120]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨47649521094,63709375160⟩,⟨-349456723869,246426943911⟩,⟨-30797873472,297416283368⟩,⟨-15286321808921,10789733827816⟩,⟨-11007687711973,7361830471358⟩,⟨-8220027790560,9274628759145⟩⟩⟩
noncomputable def wholeBoxes122 := wholeStep121.proposed :: wholeBoxes121
theorem wholeAccepted121 : StepValid wholeStep121.shape wholeBoxes121 wholeStep121.proposed := by
  dsimp only [StepValid,wholeStep121]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨28979947656750,30449753142362⟩,⟨-295512232407504,-246225036670618⟩,⟨-112048658247645,-70293272996301⟩,⟨2966503434815089,5078600779282114⟩,⟨477234634816576,2510597981100152⟩,⟨-794872229960843,1488020807853735⟩⟩⟩
noncomputable def wholeBoxes123 := wholeStep122.proposed :: wholeBoxes122
theorem wholeAccepted122 : StepValid wholeStep122.shape wholeBoxes122 wholeStep122.proposed := by
  dsimp only [StepValid,wholeStep122]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨12726217363,13342227904⟩,⟨168124888206,178754841532⟩,⟨39624054092,43248133422⟩,⟨500453983666,736409469657⟩,⟨79728274870,173378296956⟩,⟨9843947548,44341907697⟩⟩⟩
noncomputable def wholeBoxes124 := wholeStep123.proposed :: wholeBoxes123
theorem wholeAccepted123 : StepValid wholeStep123.shape wholeBoxes123 wholeStep123.proposed := by
  dsimp only [StepValid,wholeStep123]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨335426296304,369498180632⟩,⟨845337951254,2100502989169⟩,⟨-315299731614,384104637543⟩,⟨-48560638587103,6721367813804⟩,⟨-22215026252164,15644958644532⟩,⟨-18200698837358,14218225246165⟩⟩⟩
noncomputable def wholeBoxes125 := wholeStep124.proposed :: wholeBoxes124
theorem wholeAccepted124 : StepValid wholeStep124.shape wholeBoxes124 wholeStep124.proposed := by
  dsimp only [StepValid,wholeStep124]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-369498180632,-335426296304⟩,⟨-2100502989169,-845337951254⟩,⟨-384104637543,315299731614⟩,⟨-6721367813804,48560638587103⟩,⟨-15644958644532,22215026252164⟩,⟨-14218225246165,18200698837358⟩⟩⟩
noncomputable def wholeBoxes126 := wholeStep125.proposed :: wholeBoxes125
theorem wholeAccepted125 : StepValid wholeStep125.shape wholeBoxes125 wholeStep125.proposed := by
  dsimp only [StepValid,wholeStep125]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨59817306731,110689644521⟩,⟨-1297822170564,324175371236⟩,⟨-594606369664,419148771126⟩,⟨-32783367872508,34424944328959⟩,⟨-27433035703795,22682020205007⟩,⟨-23178037069334,24152513455416⟩⟩⟩
noncomputable def wholeBoxes127 := wholeStep126.proposed :: wholeBoxes126
theorem wholeAccepted126 : StepValid wholeStep126.shape wholeBoxes126 wholeStep126.proposed := by
  dsimp only [StepValid,wholeStep126]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨230980841371,233428972736⟩,⟨1584360251715,1592711161321⟩,⟨314710205396,316753821306⟩,⟨-3980232092552,-3966343577600⟩,⟨-1583382643350,-1575482923412⟩,⟨-351843720890,-351156861664⟩⟩⟩
noncomputable def wholeBoxes128 := wholeStep127.proposed :: wholeBoxes127
theorem wholeAccepted127 : StepValid wholeStep127.shape wholeBoxes127 wholeStep127.proposed := by
  dsimp only [StepValid,wholeStep127]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1706590048658,-1618563378969⟩,⟨-5608242651142,-2611040708058⟩,⟨-640471161192,1571221292783⟩,⟨-23387231373509,105977938561049⟩,⟨-65721784011918,48934824162341⟩,⟨-58999558940416,63488134433619⟩⟩⟩
noncomputable def wholeBoxes129 := wholeStep128.proposed :: wholeBoxes128
theorem wholeAccepted128 : StepValid wholeStep128.shape wholeBoxes128 wholeStep128.proposed := by
  dsimp only [StepValid,wholeStep128]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-187993776806,-174132351596⟩,⟨-1877130084604,-1431130789055⟩,⟨-375238727267,-98005331442⟩,⟨-7699035676931,12261331680917⟩,⟨-7917742943484,7394922816972⟩,⟨-6551762263224,7919965755539⟩⟩⟩
noncomputable def wholeBoxes130 := wholeStep129.proposed :: wholeBoxes129
theorem wholeAccepted129 : StepValid wholeStep129.shape wholeBoxes129 wholeStep129.proposed := by
  dsimp only [StepValid,wholeStep129]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨42987064565,59296621140⟩,⟨-292769832889,161580372266⟩,⟨-60528521871,218748489864⟩,⟨-11679267769483,8294988103317⟩,⟨-9501125586834,5819439893560⟩,⟨-6903605984114,7568808893875⟩⟩⟩
noncomputable def wholeBoxes131 := wholeStep130.proposed :: wholeBoxes130
theorem wholeAccepted130 : StepValid wholeStep130.shape wholeBoxes130 wholeStep130.proposed := by
  dsimp only [StepValid,wholeStep130]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨2592301842,6413727615⟩,⟨-110380533531,43592009358⟩,⟨-37553951138,54228265971⟩,⟨-4020223161502,3905887627093⟩,⟨-3182048276556,2332071708711⟩,⟨-2492216887075,2559927671043⟩⟩⟩
noncomputable def wholeBoxes132 := wholeStep131.proposed :: wholeBoxes131
theorem wholeAccepted131 : StepValid wholeStep131.shape wholeBoxes131 wholeStep131.proposed := by
  dsimp only [StepValid,wholeStep131]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨1680644090,3197864570⟩,⟨-31578132370,17428046920⟩,⟨-6528601862,23594195826⟩,⟨-1345773807237,1050609975162⟩,⟨-1141284161620,691977375102⟩,⟨-768706797852,903411446925⟩⟩⟩
noncomputable def wholeBoxes133 := wholeStep132.proposed :: wholeBoxes132
theorem wholeAccepted132 : StepValid wholeStep132.shape wholeBoxes132 wholeStep132.proposed := by
  dsimp only [StepValid,wholeStep132]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨3025907645,5806089209⟩,⟨-81609061992,19447838402⟩,⟨-22642467481,37402122233⟩,⟨-2650651590118,2530760970398⟩,⟨-2270743518635,1503140521437⟩,⟨-1543372593570,1712514996803⟩⟩⟩
noncomputable def wholeBoxes134 := wholeStep133.proposed :: wholeBoxes133
theorem wholeAccepted133 : StepValid wholeStep133.shape wholeBoxes133 wholeStep133.proposed := by
  dsimp only [StepValid,wholeStep133]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-5806089209,-3025907645⟩,⟨-19447838402,81609061992⟩,⟨-37402122233,22642467481⟩,⟨-2530760970398,2650651590118⟩,⟨-1503140521437,2270743518635⟩,⟨-1712514996803,1543372593570⟩⟩⟩
noncomputable def wholeBoxes135 := wholeStep134.proposed :: wholeBoxes134
theorem wholeAccepted134 : StepValid wholeStep134.shape wholeBoxes134 wholeStep134.proposed := by
  dsimp only [StepValid,wholeStep134]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨-3213787367,3387819970⟩,⟨-129828371933,125201071350⟩,⟨-74956073371,76870733452⟩,⟨-6550984131900,6556539217211⟩,⟨-4685188797993,4602815227346⟩,⟨-4204731883878,4103300264613⟩⟩⟩
noncomputable def wholeBoxes136 := wholeStep135.proposed :: wholeBoxes135
theorem wholeAccepted135 : StepValid wholeStep135.shape wholeBoxes135 wholeStep135.proposed := by
  dsimp only [StepValid,wholeStep135]
  exact ⟨by decide,by decide⟩
noncomputable def wholeProgram : List (Instruction 40) := [wholeStep0,wholeStep1,wholeStep2,wholeStep3,wholeStep4,wholeStep5,wholeStep6,wholeStep7,wholeStep8,wholeStep9,wholeStep10,wholeStep11,wholeStep12,wholeStep13,wholeStep14,wholeStep15,wholeStep16,wholeStep17,wholeStep18,wholeStep19,wholeStep20,wholeStep21,wholeStep22,wholeStep23,wholeStep24,wholeStep25,wholeStep26,wholeStep27,wholeStep28,wholeStep29,wholeStep30,wholeStep31,wholeStep32,wholeStep33,wholeStep34,wholeStep35,wholeStep36,wholeStep37,wholeStep38,wholeStep39,wholeStep40,wholeStep41,wholeStep42,wholeStep43,wholeStep44,wholeStep45,wholeStep46,wholeStep47,wholeStep48,wholeStep49,wholeStep50,wholeStep51,wholeStep52,wholeStep53,wholeStep54,wholeStep55,wholeStep56,wholeStep57,wholeStep58,wholeStep59,wholeStep60,wholeStep61,wholeStep62,wholeStep63,wholeStep64,wholeStep65,wholeStep66,wholeStep67,wholeStep68,wholeStep69,wholeStep70,wholeStep71,wholeStep72,wholeStep73,wholeStep74,wholeStep75,wholeStep76,wholeStep77,wholeStep78,wholeStep79,wholeStep80,wholeStep81,wholeStep82,wholeStep83,wholeStep84,wholeStep85,wholeStep86,wholeStep87,wholeStep88,wholeStep89,wholeStep90,wholeStep91,wholeStep92,wholeStep93,wholeStep94,wholeStep95,wholeStep96,wholeStep97,wholeStep98,wholeStep99,wholeStep100,wholeStep101,wholeStep102,wholeStep103,wholeStep104,wholeStep105,wholeStep106,wholeStep107,wholeStep108,wholeStep109,wholeStep110,wholeStep111,wholeStep112,wholeStep113,wholeStep114,wholeStep115,wholeStep116,wholeStep117,wholeStep118,wholeStep119,wholeStep120,wholeStep121,wholeStep122,wholeStep123,wholeStep124,wholeStep125,wholeStep126,wholeStep127,wholeStep128,wholeStep129,wholeStep130,wholeStep131,wholeStep132,wholeStep133,wholeStep134,wholeStep135]
theorem wholeAccepted : Accepted wholeProgram wholeInitial :=
  ⟨wholeAccepted0,⟨wholeAccepted1,⟨wholeAccepted2,⟨wholeAccepted3,⟨wholeAccepted4,⟨wholeAccepted5,⟨wholeAccepted6,⟨wholeAccepted7,⟨wholeAccepted8,⟨wholeAccepted9,⟨wholeAccepted10,⟨wholeAccepted11,⟨wholeAccepted12,⟨wholeAccepted13,⟨wholeAccepted14,⟨wholeAccepted15,⟨wholeAccepted16,⟨wholeAccepted17,⟨wholeAccepted18,⟨wholeAccepted19,⟨wholeAccepted20,⟨wholeAccepted21,⟨wholeAccepted22,⟨wholeAccepted23,⟨wholeAccepted24,⟨wholeAccepted25,⟨wholeAccepted26,⟨wholeAccepted27,⟨wholeAccepted28,⟨wholeAccepted29,⟨wholeAccepted30,⟨wholeAccepted31,⟨wholeAccepted32,⟨wholeAccepted33,⟨wholeAccepted34,⟨wholeAccepted35,⟨wholeAccepted36,⟨wholeAccepted37,⟨wholeAccepted38,⟨wholeAccepted39,⟨wholeAccepted40,⟨wholeAccepted41,⟨wholeAccepted42,⟨wholeAccepted43,⟨wholeAccepted44,⟨wholeAccepted45,⟨wholeAccepted46,⟨wholeAccepted47,⟨wholeAccepted48,⟨wholeAccepted49,⟨wholeAccepted50,⟨wholeAccepted51,⟨wholeAccepted52,⟨wholeAccepted53,⟨wholeAccepted54,⟨wholeAccepted55,⟨wholeAccepted56,⟨wholeAccepted57,⟨wholeAccepted58,⟨wholeAccepted59,⟨wholeAccepted60,⟨wholeAccepted61,⟨wholeAccepted62,⟨wholeAccepted63,⟨wholeAccepted64,⟨wholeAccepted65,⟨wholeAccepted66,⟨wholeAccepted67,⟨wholeAccepted68,⟨wholeAccepted69,⟨wholeAccepted70,⟨wholeAccepted71,⟨wholeAccepted72,⟨wholeAccepted73,⟨wholeAccepted74,⟨wholeAccepted75,⟨wholeAccepted76,⟨wholeAccepted77,⟨wholeAccepted78,⟨wholeAccepted79,⟨wholeAccepted80,⟨wholeAccepted81,⟨wholeAccepted82,⟨wholeAccepted83,⟨wholeAccepted84,⟨wholeAccepted85,⟨wholeAccepted86,⟨wholeAccepted87,⟨wholeAccepted88,⟨wholeAccepted89,⟨wholeAccepted90,⟨wholeAccepted91,⟨wholeAccepted92,⟨wholeAccepted93,⟨wholeAccepted94,⟨wholeAccepted95,⟨wholeAccepted96,⟨wholeAccepted97,⟨wholeAccepted98,⟨wholeAccepted99,⟨wholeAccepted100,⟨wholeAccepted101,⟨wholeAccepted102,⟨wholeAccepted103,⟨wholeAccepted104,⟨wholeAccepted105,⟨wholeAccepted106,⟨wholeAccepted107,⟨wholeAccepted108,⟨wholeAccepted109,⟨wholeAccepted110,⟨wholeAccepted111,⟨wholeAccepted112,⟨wholeAccepted113,⟨wholeAccepted114,⟨wholeAccepted115,⟨wholeAccepted116,⟨wholeAccepted117,⟨wholeAccepted118,⟨wholeAccepted119,⟨wholeAccepted120,⟨wholeAccepted121,⟨wholeAccepted122,⟨wholeAccepted123,⟨wholeAccepted124,⟨wholeAccepted125,⟨wholeAccepted126,⟨wholeAccepted127,⟨wholeAccepted128,⟨wholeAccepted129,⟨wholeAccepted130,⟨wholeAccepted131,⟨wholeAccepted132,⟨wholeAccepted133,⟨wholeAccepted134,⟨wholeAccepted135,True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
noncomputable def whole_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨47649521094,63709375160⟩,⟨-349456723869,246426943911⟩,⟨-30797873472,297416283368⟩,⟨-15286321808921,10789733827816⟩,⟨-11007687711973,7361830471358⟩,⟨-8220027790560,9274628759145⟩⟩
theorem whole_m11_eq : (finalBoxes wholeProgram wholeInitial).getD 14 (zeroBox 40)=whole_m11 := rfl
noncomputable def whole_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨-3213787367,3387819970⟩,⟨-129828371933,125201071350⟩,⟨-74956073371,76870733452⟩,⟨-6550984131900,6556539217211⟩,⟨-4685188797993,4602815227346⟩,⟨-4204731883878,4103300264613⟩⟩
theorem whole_kdet_eq : (finalBoxes wholeProgram wholeInitial).getD 0 (zeroBox 40)=whole_kdet := rfl
theorem sameShape : shapes centerProgram=shapes wholeProgram := by decide
theorem kernelShape : shapes wholeProgram =
    shapes CorrectionFactorizedProgramKernel.kernelProgram := by decide
attribute [local irreducible] wholeProgram centerProgram
noncomputable def inputJets (u rho : ℝ) : List BivariateJet2 :=
  [BivariateJet2.affineA (513/5120) u, BivariateJet2.affineZ (521/5120) rho,
    BivariateJet2.const 1, BivariateJet2.const 2]
noncomputable def outputJet_m11 (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 14 zeroJet
theorem output_value_m11 (u rho t : ℝ) : (outputJet_m11 u rho).value t =
    Correction.Natural.m11 (513/5120+t*(u-(513/5120))) ((513/5120+t*(u-(513/5120)))+(521/5120+t*(rho-(521/5120)))*(1/2-(513/5120+t*(u-(513/5120))))) := by
  exact CorrectionFactorizedProgramKernel.output_value_m11_of_shapes wholeProgram kernelShape (513/5120) (521/5120) u rho t
theorem output_value_one_m11 (u rho : ℝ) : (outputJet_m11 u rho).value 1 =
    Correction.Natural.m11 u (u+rho*(1/2-u)) := by simp [output_value_m11]
noncomputable def outputJet_kdet (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 0 zeroJet
theorem output_value_kdet (u rho t : ℝ) : (outputJet_kdet u rho).value t =
    Correction.Natural.kdet (513/5120+t*(u-(513/5120))) ((513/5120+t*(u-(513/5120)))+(521/5120+t*(rho-(521/5120)))*(1/2-(513/5120+t*(u-(513/5120))))) := by
  exact CorrectionFactorizedProgramKernel.output_value_kdet_of_shapes wholeProgram kernelShape (513/5120) (521/5120) u rho t
theorem output_value_one_kdet (u rho : ℝ) : (outputJet_kdet u rho).value 1 =
    Correction.Natural.kdet u (u+rho*(1/2-u)) := by simp [output_value_kdet]

private theorem center_A (x : ℝ) :
    (⟨⟨110165911142,110165911143⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩ : DyadicBivariateJetEnclosure 40).Contains (BivariateJet2.affineA (513/5120) x) 0 := by
  apply DyadicBivariateJetEnclosure.contains_coordinateA
  norm_num [DyadicInterval.Contains,DyadicInterval.scale]
private theorem whole_A {x t : ℝ} (hx : x∈Icc (1/10:ℝ) (257/2560)) (ht : t∈Icc (0:ℝ) 1) :
    (⟨⟨109951162777,110380659508⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩ : DyadicBivariateJetEnclosure 40).Contains (BivariateJet2.affineA (513/5120) x) t := by
  apply DyadicBivariateJetEnclosure.contains_coordinateA
  change (⟨109951162777,110380659508⟩ : DyadicInterval 40).Contains ((Jet2.segment (513/5120) x).value t)
  apply DyadicInterval.contains_segment _ _ ht
  · norm_num [DyadicInterval.Contains,DyadicInterval.scale]
  · norm_num [DyadicInterval.Contains,DyadicInterval.scale]
    constructor <;> linarith [hx.1,hx.2]
private theorem center_Z (x : ℝ) :
    (⟨⟨111883898060,111883898061⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩ : DyadicBivariateJetEnclosure 40).Contains (BivariateJet2.affineZ (521/5120) x) 0 := by
  apply DyadicBivariateJetEnclosure.contains_coordinateZ
  norm_num [DyadicInterval.Contains,DyadicInterval.scale]
private theorem whole_Z {x t : ℝ} (hx : x∈Icc (1/10:ℝ) (53/512)) (ht : t∈Icc (0:ℝ) 1) :
    (⟨⟨109951162777,113816633344⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩ : DyadicBivariateJetEnclosure 40).Contains (BivariateJet2.affineZ (521/5120) x) t := by
  apply DyadicBivariateJetEnclosure.contains_coordinateZ
  change (⟨109951162777,113816633344⟩ : DyadicInterval 40).Contains ((Jet2.segment (521/5120) x).value t)
  apply DyadicInterval.contains_segment _ _ ht
  · norm_num [DyadicInterval.Contains,DyadicInterval.scale]
  · norm_num [DyadicInterval.Contains,DyadicInterval.scale]
    constructor <;> linarith [hx.1,hx.2]
theorem initial_center (a z : ℝ) : RegistersContain centerInitial (inputJets a z) 0 := by
  simpa [centerInitial,inputJets,DyadicBivariateJetEnclosure.const,DyadicInterval.ofInt,DyadicInterval.scale] using
    ((((RegistersContain.nil 40 0).cons (DyadicBivariateJetEnclosure.contains_const 40 2 0)).cons
      (DyadicBivariateJetEnclosure.contains_const 40 1 0)).cons (center_Z z)).cons (center_A a)

theorem initial_whole {a z : ℝ} (ha : a ∈ Icc (1/10:ℝ) (257/2560))
    (hz : z ∈ Icc (1/10:ℝ) (53/512)) :
    ∀ t ∈ Icc (0:ℝ) 1, RegistersContain wholeInitial (inputJets a z) t := by
  intro t ht
  simpa [wholeInitial,inputJets,DyadicBivariateJetEnclosure.const,DyadicInterval.ofInt,DyadicInterval.scale] using
    ((((RegistersContain.nil 40 t).cons (DyadicBivariateJetEnclosure.contains_const 40 2 t)).cons
      (DyadicBivariateJetEnclosure.contains_const 40 1 t)).cons (whole_Z hz ht)).cons (whole_A ha ht)

theorem initial_sound (a z : ℝ) : ∀ i, ((inputJets a z).getD i zeroJet).DirectionalSoundOn
    (a-513/5120) (z-521/5120) (Icc (0:ℝ) 1) := by
  intro i t ht
  have hconst (c : ℝ) : (BivariateJet2.const c).DirectionalSoundAt (a-513/5120) (z-521/5120) t := by
    simpa only [BivariateJet2.DirectionalSoundAt,BivariateJet2.projection_const] using Jet2.soundAt_const c t
  have h : RegistersSound (inputJets a z) (a-513/5120) (z-521/5120) t :=
    ((((RegistersSound.nil _ _ t).cons (hconst 2)).cons (hconst 1)).cons
      (BivariateJet2.soundOn_affineZ (521/5120) z (a-513/5120) _ t ht)).cons
      (BivariateJet2.soundOn_affineA (513/5120) a (z-521/5120) _ t ht)
  exact h i

theorem taylor_positive_m11 : 0 < BivariateJetEnclosure.taylorLower
    center_m11.toReal whole_m11.toReal (1/5120) (9/5120) := by
  norm_num [BivariateJetEnclosure.taylorLower,JetBounds.Interval.magnitude,
    DyadicBivariateJetEnclosure.toReal,DyadicInterval.toReal,DyadicInterval.scale,center_m11,whole_m11]
theorem positive_m11 {a z : ℝ} (ha : a∈Icc (1/10:ℝ) (257/2560))
    (hz : z∈Icc (1/10:ℝ) (53/512)) : 0 < Correction.Natural.m11 a (a+z*(1/2-a)) := by
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
theorem positive_kdet {a z : ℝ} (ha : a∈Icc (1/10:ℝ) (257/2560))
    (hz : z∈Icc (1/10:ℝ) (53/512)) : 0 < Correction.Natural.kdet a (a+z*(1/2-a)) := by
  have hp := value_pos_of_accepted_taylor centerProgram wholeProgram 0 sameShape
    (initial_center a z) (initial_whole ha hz) (initial_sound a z) centerAccepted wholeAccepted
    (show (0:ℝ)≤1/5120 by norm_num) (show (0:ℝ)≤9/5120 by norm_num)
    (by rw [abs_le]; constructor <;> linarith [ha.1,ha.2])
    (by rw [abs_le]; constructor <;> linarith [hz.1,hz.2])
    (by rw [center_kdet_eq,whole_kdet_eq]; exact taylor_positive_kdet)
  change 0 < (outputJet_kdet a z).value 1 at hp
  simpa only [output_value_one_kdet] using hp

theorem _root_.solution {u rho : ℝ} (hu : u∈Icc (1/10:ℝ) (257/2560))
    (hr : rho∈Icc (1/10:ℝ) (53/512)) (hr1 : rho < 1) :
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




end GeneralCK.Certificates.LaneCB.RB2Cell000000
end

