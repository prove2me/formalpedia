-- Prove2me | solution 1 for GeneralCK.Certificates.LaneCB.RB2Cell000058.actual_minors_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-25T17:02:34.231345+00:00
-- url     : https://prove2.me/submissions/70f5e326-b3b6-4dd9-b4da-3d18d006d0b6

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

namespace LaneCBRB2Cell000058Endpoints
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

noncomputable def out_w4 : DyadicInterval 40 := ⟨-2093861750144,-2093861711424⟩
theorem checked_w4 : DyadicFastLog.check 163737617038 1099511627776 2 16 (lift40 out_w4)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w4 : out_w4.Contains (Real.log ((163737617038:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w4

noncomputable def out_w5 : DyadicInterval 40 := ⟨-2093861750144,-2093861711360⟩
theorem checked_w5 : DyadicFastLog.check 163737617041 1099511627776 2 16 (lift40 out_w5)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w5 : out_w5.Contains (Real.log ((163737617041:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w5

noncomputable def out_w6 : DyadicInterval 40 := ⟨-177293368896,-177293368832⟩
theorem checked_w6 : DyadicFastLog.check 935774010735 1099511627776 0 16 (lift40 out_w6)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w6 : out_w6.Contains (Real.log ((935774010735:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w6

noncomputable def out_w7 : DyadicInterval 40 := ⟨-177293368896,-177293368832⟩
theorem checked_w7 : DyadicFastLog.check 935774010738 1099511627776 0 16 (lift40 out_w7)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w7 : out_w7.Contains (Real.log ((935774010738:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w7

noncomputable def out_w8 : DyadicInterval 40 := ⟨762123383616,762123402880⟩
theorem checked_w8 : DyadicFastLog.check 1099511627776 2199023255552 1 16 (lift40 out_w8.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w8 : out_w8.Contains (Real.log ((2199023255552:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w8

noncomputable def out_w9 : DyadicInterval 40 := ⟨88998907456,88998907520⟩
theorem checked_w9 : DyadicFastLog.check 1099511627776 1192211685376 0 16 (lift40 out_w9.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w9 : out_w9.Contains (Real.log ((1192211685376:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w9

noncomputable def out_w10 : DyadicInterval 40 := ⟨-96842378624,-96842378560⟩
theorem checked_w10 : DyadicFastLog.check 1006811570176 1099511627776 0 16 (lift40 out_w10)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w10 : out_w10.Contains (Real.log ((1006811570176:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w10

noncomputable def out_w11 : DyadicInterval 40 := ⟨88999033728,88999033792⟩
theorem checked_w11 : DyadicFastLog.check 1099511627776 1192211822336 0 16 (lift40 out_w11.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w11 : out_w11.Contains (Real.log ((1192211822336:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w11

noncomputable def out_w12 : DyadicInterval 40 := ⟨-96842528192,-96842528128⟩
theorem checked_w12 : DyadicFastLog.check 1006811433216 1099511627776 0 16 (lift40 out_w12)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w12 : out_w12.Contains (Real.log ((1006811433216:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w12

noncomputable def out_w13 : DyadicInterval 40 := ⟨-7843494400,-7843494336⟩
theorem checked_w13 : DyadicFastLog.check 1091696043243 1099511627776 0 16 (lift40 out_w13)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w13 : out_w13.Contains (Real.log ((1091696043243:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w13

noncomputable def out_w14 : DyadicInterval 40 := ⟨-7843471168,-7843471104⟩
theorem checked_w14 : DyadicFastLog.check 1091696066338 1099511627776 0 16 (lift40 out_w14)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w14 : out_w14.Contains (Real.log ((1091696066338:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w14

noncomputable def out_w15 : DyadicInterval 40 := ⟨185841286016,185841286080⟩
theorem checked_w15 : DyadicFastLog.check 1099511627776 1301982068612 0 16 (lift40 out_w15.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w15 : out_w15.Contains (Real.log ((1301982068612:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w15

noncomputable def out_w16 : DyadicInterval 40 := ⟨185841561920,185841561984⟩
theorem checked_w16 : DyadicFastLog.check 1099511627776 1301982395298 0 16 (lift40 out_w16.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w16 : out_w16.Contains (Real.log ((1301982395298:ℝ)/1099511627776)) := by
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

noncomputable def out_w19 : DyadicInterval 40 := ⟨1916568342528,1916568381120⟩
theorem checked_w19 : DyadicFastLog.check 1099511627776 6283799803414 2 16 (lift40 out_w19.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w19 : out_w19.Contains (Real.log ((6283799803414:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w19

noncomputable def out_w20 : DyadicInterval 40 := ⟨1916568342528,1916568381120⟩
theorem checked_w20 : DyadicFastLog.check 1099511627776 6283799803550 2 16 (lift40 out_w20.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w20 : out_w20.Contains (Real.log ((6283799803550:ℝ)/1099511627776)) := by
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

noncomputable def out_w25 : DyadicInterval 40 := ⟨-2100642521216,-2100642482432⟩
theorem checked_w25 : DyadicFastLog.check 162730942135 1099511627776 2 16 (lift40 out_w25)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w25 : out_w25.Contains (Real.log ((162730942135:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w25

noncomputable def out_w26 : DyadicInterval 40 := ⟨-2087117501760,-2087117463040⟩
theorem checked_w26 : DyadicFastLog.check 164745046918 1099511627776 2 16 (lift40 out_w26)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w26 : out_w26.Contains (Real.log ((164745046918:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w26

noncomputable def out_w27 : DyadicInterval 40 := ⟨-178477712064,-178477712000⟩
theorem checked_w27 : DyadicFastLog.check 934766580858 1099511627776 0 16 (lift40 out_w27)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w27 : out_w27.Contains (Real.log ((934766580858:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w27

noncomputable def out_w28 : DyadicInterval 40 := ⟨-176111186240,-176111186176⟩
theorem checked_w28 : DyadicFastLog.check 936780685641 1099511627776 0 16 (lift40 out_w28)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w28 : out_w28.Contains (Real.log ((936780685641:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w28

noncomputable def out_w29 : DyadicInterval 40 := ⟨86449976896,86449976960⟩
theorem checked_w29 : DyadicFastLog.check 1099511627776 1189451055104 0 16 (lift40 out_w29.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w29 : out_w29.Contains (Real.log ((1189451055104:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w29

noncomputable def out_w30 : DyadicInterval 40 := ⟨-93831694784,-93831694720⟩
theorem checked_w30 : DyadicFastLog.check 1009572200448 1099511627776 0 16 (lift40 out_w30)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w30 : out_w30.Contains (Real.log ((1009572200448:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w30

noncomputable def out_w31 : DyadicInterval 40 := ⟨91569557376,91569557440⟩
theorem checked_w31 : DyadicFastLog.check 1099511627776 1195002328320 0 16 (lift40 out_w31.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w31 : out_w31.Contains (Real.log ((1195002328320:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w31

noncomputable def out_w32 : DyadicInterval 40 := ⟨-99894195520,-99894195456⟩
theorem checked_w32 : DyadicFastLog.check 1004020927232 1099511627776 0 16 (lift40 out_w32)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w32 : out_w32.Contains (Real.log ((1004020927232:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w32

noncomputable def out_w33 : DyadicInterval 40 := ⟨-8324638144,-8324638080⟩
theorem checked_w33 : DyadicFastLog.check 1091218424084 1099511627776 0 16 (lift40 out_w33)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w33 : out_w33.Contains (Real.log ((1091218424084:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w33

noncomputable def out_w34 : DyadicInterval 40 := ⟨-7381717888,-7381717824⟩
theorem checked_w34 : DyadicFastLog.check 1092154633650 1099511627776 0 16 (lift40 out_w34)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w34 : out_w34.Contains (Real.log ((1092154633650:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w34

noncomputable def out_w35 : DyadicInterval 40 := ⟨180281671680,180281671744⟩
theorem checked_w35 : DyadicFastLog.check 1099511627776 1295415290928 0 16 (lift40 out_w35.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w35 : out_w35.Contains (Real.log ((1295415290928:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w35

noncomputable def out_w36 : DyadicInterval 40 := ⟨191463752896,191463752960⟩
theorem checked_w36 : DyadicFastLog.check 1099511627776 1308656940878 0 16 (lift40 out_w36.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w36 : out_w36.Contains (Real.log ((1308656940878:ℝ)/1099511627776)) := by
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

noncomputable def out_w39 : DyadicInterval 40 := ⟨1908639750976,1908639789568⟩
theorem checked_w39 : DyadicFastLog.check 1099511627776 6238650230385 2 16 (lift40 out_w39.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w39 : out_w39.Contains (Real.log ((6238650230385:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w39

noncomputable def out_w40 : DyadicInterval 40 := ⟨1924531296256,1924531334848⟩
theorem checked_w40 : DyadicFastLog.check 1099511627776 6329473934243 2 16 (lift40 out_w40.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w40 : out_w40.Contains (Real.log ((6329473934243:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w40

end LaneCBRB2Cell000058Endpoints

namespace GeneralCK.Certificates.LaneCB.RB2Cell000058
open Set LaneCBRB2Cell000058Endpoints
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
theorem lc2 : ProvedTranscendental.LogEncloses (⟨163737617038,163737617041⟩ : DyadicInterval 40) (⟨-2093861750144,-2093861711360⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w4
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w5
theorem lc3 : ProvedTranscendental.LogEncloses (⟨935774010735,935774010738⟩ : DyadicInterval 40) (⟨-177293368896,-177293368832⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w6
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w7
theorem lc4 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
theorem lc5 : ProvedTranscendental.LogEncloses (⟨1192211685376,1192211685376⟩ : DyadicInterval 40) (⟨88998907456,88998907520⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w9
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w9
theorem lc6 : ProvedTranscendental.LogEncloses (⟨1006811570176,1006811570176⟩ : DyadicInterval 40) (⟨-96842378624,-96842378560⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w10
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w10
theorem lc7 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
theorem lc8 : ProvedTranscendental.LogEncloses (⟨1192211822336,1192211822336⟩ : DyadicInterval 40) (⟨88999033728,88999033792⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w11
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w11
theorem lc9 : ProvedTranscendental.LogEncloses (⟨1006811433216,1006811433216⟩ : DyadicInterval 40) (⟨-96842528192,-96842528128⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w12
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w12
theorem lc10 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
theorem lc11 : ProvedTranscendental.LogEncloses (⟨1091696043243,1091696066338⟩ : DyadicInterval 40) (⟨-7843494400,-7843471104⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w13
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w14
theorem lc12 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
theorem lc13 : ProvedTranscendental.LogEncloses (⟨1192211685376,1192211822336⟩ : DyadicInterval 40) (⟨88998907456,88999033792⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w9
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w11
theorem lc14 : ProvedTranscendental.LogEncloses (⟨1006811433216,1006811570176⟩ : DyadicInterval 40) (⟨-96842528192,-96842378560⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w12
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w10
theorem lc15 : ProvedTranscendental.LogEncloses (⟨1091696043243,1091696066338⟩ : DyadicInterval 40) (⟨-7843494400,-7843471104⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w13
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w14
theorem lc16 : ProvedTranscendental.LogEncloses (⟨1301982068612,1301982395298⟩ : DyadicInterval 40) (⟨185841286016,185841561984⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w15
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w16
theorem lc17 : ProvedTranscendental.LogEncloses (⟨9582650676195,9582650676291⟩ : DyadicInterval 40) (⟨2380539576896,2380539634752⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w17
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w18
theorem lc18 : ProvedTranscendental.LogEncloses (⟨6283799803414,6283799803550⟩ : DyadicInterval 40) (⟨1916568342528,1916568381120⟩ : DyadicInterval 40) := by
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
theorem lc21 : ProvedTranscendental.LogEncloses (⟨162730942135,164745046918⟩ : DyadicInterval 40) (⟨-2100642521216,-2087117463040⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w25
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w26
theorem lc22 : ProvedTranscendental.LogEncloses (⟨934766580858,936780685641⟩ : DyadicInterval 40) (⟨-178477712064,-176111186176⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w27
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w28
theorem lc23 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
theorem lc24 : ProvedTranscendental.LogEncloses (⟨1189451055104,1189451055104⟩ : DyadicInterval 40) (⟨86449976896,86449976960⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w29
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w29
theorem lc25 : ProvedTranscendental.LogEncloses (⟨1009572200448,1009572200448⟩ : DyadicInterval 40) (⟨-93831694784,-93831694720⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w30
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w30
theorem lc26 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
theorem lc27 : ProvedTranscendental.LogEncloses (⟨1195002328320,1195002328320⟩ : DyadicInterval 40) (⟨91569557376,91569557440⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w31
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w31
theorem lc28 : ProvedTranscendental.LogEncloses (⟨1004020927232,1004020927232⟩ : DyadicInterval 40) (⟨-99894195520,-99894195456⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w32
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w32
theorem lc29 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
theorem lc30 : ProvedTranscendental.LogEncloses (⟨1091218424084,1092154633650⟩ : DyadicInterval 40) (⟨-8324638144,-7381717824⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w33
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w34
theorem lc31 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
theorem lc32 : ProvedTranscendental.LogEncloses (⟨1189451055104,1195002328320⟩ : DyadicInterval 40) (⟨86449976896,91569557440⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w29
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w31
theorem lc33 : ProvedTranscendental.LogEncloses (⟨1004020927232,1009572200448⟩ : DyadicInterval 40) (⟨-99894195520,-93831694720⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w32
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w30
theorem lc34 : ProvedTranscendental.LogEncloses (⟨1091218424084,1092154633650⟩ : DyadicInterval 40) (⟨-8324638144,-7381717824⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w33
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w34
theorem lc35 : ProvedTranscendental.LogEncloses (⟨1295415290928,1308656940878⟩ : DyadicInterval 40) (⟨180281671680,191463752960⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w35
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w36
theorem lc36 : ProvedTranscendental.LogEncloses (⟨9562419308177,9602958969664⟩ : DyadicInterval 40) (⟨2378215779456,2382867339072⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w37
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w38
theorem lc37 : ProvedTranscendental.LogEncloses (⟨6238650230385,6329473934243⟩ : DyadicInterval 40) (⟨1908639750976,1924531334848⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w39
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w40
theorem ew11_ok (x : ℝ) (hx : (⟨92700057600,92700057600⟩ : DyadicInterval 40).Contains x) : (⟨758210960092,758210979422⟩ : DyadicInterval 40).Contains (Reflection.biasE x) := by
  exact ProvedTranscendental.entropy_encloses (c:=(⟨92700057600,92700057600⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (plus:=(⟨88998907456,88998907520⟩ : DyadicInterval 40)) (minus:=(⟨-96842378624,-96842378560⟩ : DyadicInterval 40))
    (lc4 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc5 lc6 (by decide) hx
theorem ew14_ok (x : ℝ) (hx : (⟨92700194560,92700194560⟩ : DyadicInterval 40).Contains x) : (⟨758210948537,758210967867⟩ : DyadicInterval 40).Contains (Reflection.biasE x) := by
  exact ProvedTranscendental.entropy_encloses (c:=(⟨92700194560,92700194560⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (plus:=(⟨88999033728,88999033792⟩ : DyadicInterval 40)) (minus:=(⟨-96842528192,-96842528128⟩ : DyadicInterval 40))
    (lc7 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc8 lc9 (by decide) hx
theorem ew35_ok (x : ℝ) (hx : (⟨89939427328,89939427328⟩ : DyadicInterval 40).Contains x) : (⟨758440773266,758440792596⟩ : DyadicInterval 40).Contains (Reflection.biasE x) := by
  exact ProvedTranscendental.entropy_encloses (c:=(⟨89939427328,89939427328⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (plus:=(⟨86449976896,86449976960⟩ : DyadicInterval 40)) (minus:=(⟨-93831694784,-93831694720⟩ : DyadicInterval 40))
    (lc23 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc24 lc25 (by decide) hx
theorem ew38_ok (x : ℝ) (hx : (⟨95490700544,95490700544⟩ : DyadicInterval 40).Contains x) : (⟨757971553218,757971572547⟩ : DyadicInterval 40).Contains (Reflection.biasE x) := by
  exact ProvedTranscendental.entropy_encloses (c:=(⟨95490700544,95490700544⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (plus:=(⟨91569557376,91569557440⟩ : DyadicInterval 40)) (minus:=(⟨-99894195520,-99894195456⟩ : DyadicInterval 40))
    (lc26 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc27 lc28 (by decide) hx
theorem bw17_ok (x : ℝ) (hx : (⟨92700057600,92700194560⟩ : DyadicInterval 40).Contains x) : (⟨766045119168,766045150080⟩ : DyadicInterval 40).Contains (Reflection.biasB x) := by
  exact ProvedTranscendental.denominator_encloses (c:=(⟨92700057600,92700194560⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (gapLog:=(⟨-7843494400,-7843471104⟩ : DyadicInterval 40))
    (lc10 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc11 (by decide) hx
theorem bw41_ok (x : ℝ) (hx : (⟨89939427328,95490700544⟩ : DyadicInterval 40).Contains x) : (⟨765814242528,766285721952⟩ : DyadicInterval 40).Contains (Reflection.biasB x) := by
  exact ProvedTranscendental.denominator_encloses (c:=(⟨89939427328,95490700544⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (gapLog:=(⟨-8324638144,-7381717824⟩ : DyadicInterval 40))
    (lc29 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc30 (by decide) hx
theorem brcenter28_contact (y : ℝ) (hy : (⟨8993102542752,8993102672355⟩ : DyadicInterval 40).Contains y) : (⟨92700057600,92700194560⟩ : DyadicInterval 40).Contains (Reflection.biasContact y) := by
  exact ProvedTranscendental.contact_bracket (Y:=(⟨8993102542752,8993102672355⟩ : DyadicInterval 40)) (c:=(⟨92700057600,92700194560⟩ : DyadicInterval 40)) (elo:=(⟨758210960092,758210979422⟩ : DyadicInterval 40)) (ehi:=(⟨758210948537,758210967867⟩ : DyadicInterval 40))
    (by decide) (by decide) (by decide) (by decide)
    (ew11_ok _ (DyadicContact.point_contains 40 92700057600)) (ew14_ok _ (DyadicContact.point_contains 40 92700194560))
    (by decide) (by decide) hy
theorem brcenter28_jet (y : ℝ) (hy : (⟨8993102542752,8993102672355⟩ : DyadicInterval 40).Contains y) : (⟨⟨92700057600,92700194560⟩,⟨-11217780594,-11217746992⟩,⟨2700997622,2701009996⟩⟩ : DyadicJetEnclosure 40).Contains reflectionContactJet y := by
  exact ProvedTranscendental.contact_jet (c:=(⟨92700057600,92700194560⟩ : DyadicInterval 40)) (B:=(⟨766045119168,766045150080⟩ : DyadicInterval 40)) (by decide) brcenter28_contact bw17_ok (by decide) (by decide) (by decide) hy
theorem brwhole28_contact (y : ℝ) (hy : (⟨8727542231051,9271949548424⟩ : DyadicInterval 40).Contains y) : (⟨89939427328,95490700544⟩ : DyadicInterval 40).Contains (Reflection.biasContact y) := by
  exact ProvedTranscendental.contact_bracket (Y:=(⟨8727542231051,9271949548424⟩ : DyadicInterval 40)) (c:=(⟨89939427328,95490700544⟩ : DyadicInterval 40)) (elo:=(⟨758440773266,758440792596⟩ : DyadicInterval 40)) (ehi:=(⟨757971553218,757971572547⟩ : DyadicInterval 40))
    (by decide) (by decide) (by decide) (by decide)
    (ew35_ok _ (DyadicContact.point_contains 40 89939427328)) (ew38_ok _ (DyadicContact.point_contains 40 95490700544))
    (by decide) (by decide) hy
theorem brwhole28_jet (y : ℝ) (hy : (⟨8727542231051,9271949548424⟩ : DyadicInterval 40).Contains y) : (⟨⟨89939427328,95490700544⟩,⟨-11906900375,-10556245999⟩,⟨2461785876,2957408433⟩⟩ : DyadicJetEnclosure 40).Contains reflectionContactJet y := by
  exact ProvedTranscendental.contact_jet (c:=(⟨89939427328,95490700544⟩ : DyadicInterval 40)) (B:=(⟨765814242528,766285721952⟩ : DyadicInterval 40)) (by decide) brwhole28_contact bw41_ok (by decide) (by decide) (by decide) hy
noncomputable def centerInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨113172388249,113172388250⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨127345780326,127345780327⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
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
noncomputable def centerStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨50565228789,50565228791⟩,⟨-127345780327,-127345780326⟩,⟨436583425638,436583425639⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes5 := centerStep4.proposed :: centerBoxes4
theorem centerAccepted4 : StepValid centerStep4.shape centerBoxes4 centerStep4.proposed := by
  dsimp only [StepValid,centerStep4]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨163737617038,163737617041⟩,⟨972165847449,972165847450⟩,⟨436583425638,436583425639⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes6 := centerStep5.proposed :: centerBoxes5
theorem centerAccepted5 : StepValid centerStep5.shape centerBoxes5 centerStep5.proposed := by
  dsimp only [StepValid,centerStep5]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨50565228788,50565228792⟩,⟨-127345780327,-127345780326⟩,⟨436583425638,436583425639⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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
noncomputable def centerStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2093861750144,-2093861711360⟩,⟨6528173993940,6528173994068⟩,⟨2931693777264,2931693777326⟩,⟨-38759986361423,-38759986359912⟩,⟨-24789773165996,-24789773165159⟩,⟨-7816950896094,-7816950895769⟩⟩⟩
noncomputable def centerBoxes16 := centerStep15.proposed :: centerBoxes15
theorem centerAccepted15 : StepValid centerStep15.shape centerBoxes15 centerStep15.proposed := by
  dsimp only [StepValid,centerStep15]
  exact ⟨by decide,by decide,lc2,by decide⟩
noncomputable def centerStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-311814740946,-311814735164⟩,⟨-879184180481,-879184146149⟩,⟨-394826913834,-394826898412⟩,⟨5772078841677,5772078842249⟩,⟨3586494171283,3586494210376⟩,⟨1164088564241,1164088564368⟩⟩⟩
noncomputable def centerBoxes17 := centerStep16.proposed :: centerBoxes16
theorem centerAccepted16 : StepValid centerStep16.shape centerBoxes16 centerStep16.proposed := by
  dsimp only [StepValid,centerStep16]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep17 : Instruction 40 := ⟨.neg 0,⟨⟨311814735164,311814740946⟩,⟨879184146149,879184180481⟩,⟨394826898412,394826913834⟩,⟨-5772078842249,-5772078841677⟩,⟨-3586494210376,-3586494171283⟩,⟨-1164088564368,-1164088564241⟩⟩⟩
noncomputable def centerBoxes18 := centerStep17.proposed :: centerBoxes17
theorem centerAccepted17 : StepValid centerStep17.shape centerBoxes17 centerStep17.proposed := by
  dsimp only [StepValid,centerStep17]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-163737617041,-163737617038⟩,⟨-972165847450,-972165847449⟩,⟨-436583425639,-436583425638⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes19 := centerStep18.proposed :: centerBoxes18
theorem centerAccepted18 : StepValid centerStep18.shape centerBoxes18 centerStep18.proposed := by
  dsimp only [StepValid,centerStep18]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨935774010735,935774010738⟩,⟨-972165847450,-972165847449⟩,⟨-436583425639,-436583425638⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes20 := centerStep19.proposed :: centerBoxes19
theorem centerAccepted19 : StepValid centerStep19.shape centerBoxes19 centerStep19.proposed := by
  dsimp only [StepValid,centerStep19]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep20 : Instruction 40 := ⟨.log 0,⟨⟨-177293368896,-177293368832⟩,⟨-1142271147880,-1142271147873⟩,⟨-512974871580,-512974871576⟩,⟨-1186693566778,-1186693566763⟩,⟨758975095175,758975095187⟩,⟨-239327363372,-239327363368⟩⟩⟩
noncomputable def centerBoxes21 := centerStep20.proposed :: centerBoxes20
theorem centerAccepted20 : StepValid centerStep20.shape centerBoxes20 centerStep20.proposed := by
  dsimp only [StepValid,centerStep20]
  exact ⟨by decide,by decide,lc3,by decide⟩
noncomputable def centerStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-150891107196,-150891107140⟩,⟨-815406652005,-815406651937⟩,⟨-366185492275,-366185492243⟩,⟨1009972946553,1009972946586⟩,⟨1375780220516,1375780220603⟩,⟨203687092558,203687092568⟩⟩⟩
noncomputable def centerBoxes22 := centerStep21.proposed :: centerBoxes21
theorem centerAccepted21 : StepValid centerStep21.shape centerBoxes21 centerStep21.proposed := by
  dsimp only [StepValid,centerStep21]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep22 : Instruction 40 := ⟨.neg 0,⟨⟨150891107140,150891107196⟩,⟨815406651937,815406652005⟩,⟨366185492243,366185492275⟩,⟨-1009972946586,-1009972946553⟩,⟨-1375780220603,-1375780220516⟩,⟨-203687092568,-203687092558⟩⟩⟩
noncomputable def centerBoxes23 := centerStep22.proposed :: centerBoxes22
theorem centerAccepted22 : StepValid centerStep22.shape centerBoxes22 centerStep22.proposed := by
  dsimp only [StepValid,centerStep22]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨462705842304,462705848142⟩,⟨1694590798086,1694590832486⟩,⟨761012390655,761012406109⟩,⟨-6782051788835,-6782051788230⟩,⟨-4962274430979,-4962274391799⟩,⟨-1367775656936,-1367775656799⟩⟩⟩
noncomputable def centerBoxes24 := centerStep23.proposed :: centerBoxes23
theorem centerAccepted23 : StepValid centerStep23.shape centerBoxes23 centerStep23.proposed := by
  dsimp only [StepValid,centerStep23]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨827164126575,827164138430⟩,⟨4075130374970,4075130467314⟩,⟨761012390655,761012406109⟩,⟨-18689883488747,-18689883487652⟩,⟨-4962274430979,-4962274391799⟩,⟨-1367775656936,-1367775656799⟩⟩⟩
noncomputable def centerBoxes25 := centerStep24.proposed :: centerBoxes24
theorem centerAccepted24 : StepValid centerStep24.shape centerBoxes24 centerStep24.proposed := by
  dsimp only [StepValid,centerStep24]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨101130457576,101130457584⟩,⟨-254691560654,-254691560652⟩,⟨873166851276,873166851278⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes26 := centerStep25.proposed :: centerBoxes25
theorem centerAccepted25 : StepValid centerStep25.shape centerBoxes25 centerStep25.proposed := by
  dsimp only [StepValid,centerStep25]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep26 : Instruction 40 := ⟨.inv 0,⟨⟨11954121918320,11954121919266⟩,⟨30105806305408,30105806310410⟩,⟨-103212654686102,-103212654669529⟩,⟨151639673660969,151639673699354⟩,⟨-259935460953766,-259935460783924⟩,⟨1782289348681594,1782289349112901⟩⟩⟩
noncomputable def centerBoxes27 := centerStep26.proposed :: centerBoxes26
theorem centerAccepted26 : StepValid centerStep26.shape centerBoxes26 centerStep26.proposed := by
  dsimp only [StepValid,centerStep26]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨8993102542752,8993102672355⟩,⟨66954315400734,66954316736590⟩,⟨-69373137820786,-69373136526797⟩,⟨134041259855437,134041266641323⟩,⟨-611201419129999,-611201406612850⟩,⟨1183073467543893,1183073490012102⟩⟩⟩
noncomputable def centerBoxes28 := centerStep27.proposed :: centerBoxes27
theorem centerAccepted27 : StepValid centerStep27.shape centerBoxes27 centerStep27.proposed := by
  dsimp only [StepValid,centerStep27]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep28 : Instruction 40 := ⟨.contact 0,⟨⟨92700057600,92700194560⟩,⟨-683102221022,-683100161211⟩,⟨707778138893,707780272197⟩,⟨8648151329459,8648201779542⟩,⟨-4141817808850,-4141751059268⟩,⟨-1317876996902,-1317790950850⟩⟩⟩
noncomputable def centerBoxes29 := centerStep28.proposed :: centerBoxes28
theorem centerAccepted28 : StepValid centerStep28.shape centerBoxes28 centerStep28.proposed := by
  dsimp only [StepValid,centerStep28]
  exact ⟨by decide,by decide,(⟨⟨92700057600,92700194560⟩,⟨-11217780594,-11217746992⟩,⟨2700997622,2701009996⟩⟩ : DyadicJetEnclosure 40),brcenter28_jet,by decide⟩
noncomputable def centerStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes30 := centerStep29.proposed :: centerBoxes29
theorem centerAccepted29 : StepValid centerStep29.shape centerBoxes29 centerStep29.proposed := by
  dsimp only [StepValid,centerStep29]
  exact ⟨by decide,by decide,lc4,by decide⟩
noncomputable def centerStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1192211685376,1192211822336⟩,⟨-683102221022,-683100161211⟩,⟨707778138893,707780272197⟩,⟨8648151329459,8648201779542⟩,⟨-4141817808850,-4141751059268⟩,⟨-1317876996902,-1317790950850⟩⟩⟩
noncomputable def centerBoxes31 := centerStep30.proposed :: centerBoxes30
theorem centerAccepted30 : StepValid centerStep30.shape centerBoxes30 centerStep30.proposed := by
  dsimp only [StepValid,centerStep30]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep31 : Instruction 40 := ⟨.log 0,⟨⟨88998907456,88999033792⟩,⟨-629987815240,-629985843216⟩,⟨652744989622,652747032039⟩,⟨7614751548486,7614801251907⟩,⟨-3445769518061,-3445705178792⟩,⟨-1602922180287,-1602840260062⟩⟩⟩
noncomputable def centerBoxes32 := centerStep31.proposed :: centerBoxes31
theorem centerAccepted31 : StepValid centerStep31.shape centerBoxes31 centerStep31.proposed := by
  dsimp only [StepValid,centerStep31]
  exact ⟨by decide,by decide,lc13,by decide⟩
noncomputable def centerStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨96502424143,96502572218⟩,⟨-738395427934,-738392965953⟩,⟨765068475884,765071025813⟩,⟨9739559263196,9739623993751⟩,⟨-4882613970323,-4882532914985⟩,⟨-1004368900934,-1004267595536⟩⟩⟩
noncomputable def centerBoxes33 := centerStep32.proposed :: centerBoxes32
theorem centerAccepted32 : StepValid centerStep32.shape centerBoxes32 centerStep32.proposed := by
  dsimp only [StepValid,centerStep32]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-92700194560,-92700057600⟩,⟨683100161211,683102221022⟩,⟨-707780272197,-707778138893⟩,⟨-8648201779542,-8648151329459⟩,⟨4141751059268,4141817808850⟩,⟨1317790950850,1317876996902⟩⟩⟩
noncomputable def centerBoxes34 := centerStep33.proposed :: centerBoxes33
theorem centerAccepted33 : StepValid centerStep33.shape centerBoxes33 centerStep33.proposed := by
  dsimp only [StepValid,centerStep33]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1006811433216,1006811570176⟩,⟨683100161211,683102221022⟩,⟨-707780272197,-707778138893⟩,⟨-8648201779542,-8648151329459⟩,⟨4141751059268,4141817808850⟩,⟨1317790950850,1317876996902⟩⟩⟩
noncomputable def centerBoxes35 := centerStep34.proposed :: centerBoxes34
theorem centerAccepted34 : StepValid centerStep34.shape centerBoxes34 centerStep34.proposed := by
  dsimp only [StepValid,centerStep34]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep35 : Instruction 40 := ⟨.log 0,⟨⟨-96842528192,-96842378560⟩,⟨745995171723,745997522669⟩,⟨-772947757165,-772945322293⟩,⟨-9950613044369,-9950553474288⟩,⟨5047520979912,5047597795334⟩,⟨895747776216,895845363948⟩⟩⟩
noncomputable def centerBoxes36 := centerStep35.proposed :: centerBoxes35
theorem centerAccepted35 : StepValid centerStep35.shape centerBoxes35 centerStep35.proposed := by
  dsimp only [StepValid,centerStep35]
  exact ⟨by decide,by decide,lc14,by decide⟩
noncomputable def centerStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-88677714183,-88677565103⟩,⟨622933950504,622936470555⟩,⟨-645440947294,-645438337206⟩,⟨-7423028322948,-7422961199034⟩,⟨3296730087408,3296813419570⟩,⟨1699272766474,1699376130372⟩⟩⟩
noncomputable def centerBoxes37 := centerStep36.proposed :: centerBoxes36
theorem centerAccepted36 : StepValid centerStep36.shape centerBoxes36 centerStep36.proposed := by
  dsimp only [StepValid,centerStep36]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨7824709960,7825007115⟩,⟨-115461477430,-115456495398⟩,⟨119627528590,119632688607⟩,⟨2316530940248,2316662794717⟩,⟨-1585883882915,-1585719495415⟩,⟨694903865540,695108534836⟩⟩⟩
noncomputable def centerBoxes38 := centerStep37.proposed :: centerBoxes37
theorem centerAccepted37 : StepValid centerStep37.shape centerBoxes37 centerStep37.proposed := by
  dsimp only [StepValid,centerStep37]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨3912354980,3912503558⟩,⟨-57730738715,-57728247699⟩,⟨59813764295,59816344304⟩,⟨1158265470124,1158331397359⟩,⟨-792941941458,-792859747707⟩,⟨347451932770,347554267418⟩⟩⟩
noncomputable def centerBoxes39 := centerStep38.proposed :: centerBoxes38
theorem centerAccepted38 : StepValid centerStep38.shape centerBoxes38 centerStep38.proposed := by
  dsimp only [StepValid,centerStep38]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-3912503558,-3912354980⟩,⟨57728247699,57730738715⟩,⟨-59816344304,-59813764295⟩,⟨-1158331397359,-1158265470124⟩,⟨792859747707,792941941458⟩,⟨-347554267418,-347451932770⟩⟩⟩
noncomputable def centerBoxes40 := centerStep39.proposed :: centerBoxes39
theorem centerAccepted39 : StepValid centerStep39.shape centerBoxes39 centerStep39.proposed := by
  dsimp only [StepValid,centerStep39]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨758210880058,758211047900⟩,⟨57728247699,57730738715⟩,⟨-59816344304,-59813764295⟩,⟨-1158331397359,-1158265470124⟩,⟨792859747707,792941941458⟩,⟨-347554267418,-347451932770⟩⟩⟩
noncomputable def centerBoxes41 := centerStep40.proposed :: centerBoxes40
theorem centerAccepted40 : StepValid centerStep40.shape centerBoxes40 centerStep40.proposed := by
  dsimp only [StepValid,centerStep40]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨7815561438,7815584533⟩,⟨-115185155288,-115184637780⟩,⟨119345848804,119346384852⟩,⟨2307042371503,2307058151790⟩,⟨-1577852513304,-1577834923478⟩,⟨689001244382,689021574843⟩⟩⟩
noncomputable def centerBoxes42 := centerStep41.proposed :: centerBoxes41
theorem centerAccepted41 : StepValid centerStep41.shape centerBoxes41 centerStep41.proposed := by
  dsimp only [StepValid,centerStep41]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-7815584533,-7815561438⟩,⟨115184637780,115185155288⟩,⟨-119346384852,-119345848804⟩,⟨-2307058151790,-2307042371503⟩,⟨1577834923478,1577852513304⟩,⟨-689021574843,-689001244382⟩⟩⟩
noncomputable def centerBoxes43 := centerStep42.proposed :: centerBoxes42
theorem centerAccepted42 : StepValid centerStep42.shape centerBoxes42 centerStep42.proposed := by
  dsimp only [StepValid,centerStep42]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1091696043243,1091696066338⟩,⟨115184637780,115185155288⟩,⟨-119346384852,-119345848804⟩,⟨-2307058151790,-2307042371503⟩,⟨1577834923478,1577852513304⟩,⟨-689021574843,-689001244382⟩⟩⟩
noncomputable def centerBoxes44 := centerStep43.proposed :: centerBoxes43
theorem centerAccepted43 : StepValid centerStep43.shape centerBoxes43 centerStep43.proposed := by
  dsimp only [StepValid,centerStep43]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep44 : Instruction 40 := ⟨.log 0,⟨⟨-7843494400,-7843471104⟩,⟨116009256133,116009779802⟩,⟨-120200800113,-120200257684⟩,⟨-2335814885595,-2335798832670⟩,⟨1601813107270,1601830971126⟩,⟨-707094954734,-707074345442⟩⟩⟩
noncomputable def centerBoxes45 := centerStep44.proposed :: centerBoxes44
theorem centerAccepted44 : StepValid centerStep44.shape centerBoxes44 centerStep44.proposed := by
  dsimp only [StepValid,centerStep44]
  exact ⟨by decide,by decide,lc11,by decide⟩
noncomputable def centerStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-3921747200,-3921735552⟩,⟨58004628066,58004889901⟩,⟨-60100400057,-60100128842⟩,⟨-1167907442798,-1167899416335⟩,⟨800906553635,800915485563⟩,⟨-353547477367,-353537172721⟩⟩⟩
noncomputable def centerBoxes46 := centerStep45.proposed :: centerBoxes45
theorem centerAccepted45 : StepValid centerStep45.shape centerBoxes45 centerStep45.proposed := by
  dsimp only [StepValid,centerStep45]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3921735552,3921747200⟩,⟨-58004889901,-58004628066⟩,⟨60100128842,60100400057⟩,⟨1167899416335,1167907442798⟩,⟨-800915485563,-800906553635⟩,⟨353537172721,353547477367⟩⟩⟩
noncomputable def centerBoxes47 := centerStep46.proposed :: centerBoxes46
theorem centerAccepted46 : StepValid centerStep46.shape centerBoxes46 centerStep46.proposed := by
  dsimp only [StepValid,centerStep46]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨766045119168,766045150080⟩,⟨-58004889901,-58004628066⟩,⟨60100128842,60100400057⟩,⟨1167899416335,1167907442798⟩,⟨-800915485563,-800906553635⟩,⟨353537172721,353547477367⟩⟩⟩
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
noncomputable def centerStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272924010810,272924016585⟩,⟨28796159445,28796288822⟩,⟨-29836596213,-29836462201⟩,⟨-576764537948,-576760592875⟩,⟨394458730869,394463128326⟩,⟨-172255393711,-172250311095⟩⟩⟩
noncomputable def centerBoxes51 := centerStep50.proposed :: centerBoxes50
theorem centerAccepted50 : StepValid centerStep50.shape centerBoxes50 centerStep50.proposed := by
  dsimp only [StepValid,centerStep50]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1532090238336,1532090300160⟩,⟨-116009779802,-116009256132⟩,⟨120200257684,120200800114⟩,⟨2335798832670,2335814885596⟩,⟨-1601830971126,-1601813107270⟩,⟨707074345442,707094954734⟩⟩⟩
noncomputable def centerBoxes52 := centerStep51.proposed :: centerBoxes51
theorem centerAccepted51 : StepValid centerStep51.shape centerBoxes51 centerStep51.proposed := by
  dsimp only [StepValid,centerStep51]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1200746848194,1200747011537⟩,⟨-814683786266,-814681108036⟩,⟨844112637032,844115410919⟩,⟨11419473498904,11419543591099⟩,⟨-6085061589678,-6084973264876⟩,⟨-384926186629,-384815499869⟩⟩⟩
noncomputable def centerBoxes53 := centerStep52.proposed :: centerBoxes52
theorem centerAccepted52 : StepValid centerStep52.shape centerBoxes52 centerStep52.proposed := by
  dsimp only [StepValid,centerStep52]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1301982068612,1301982395298⟩,⟨-1629367572531,-1629362216071⟩,⟨1688225274064,1688230821838⟩,⟨22838946997814,22839087182185⟩,⟨-12170123179350,-12169946529756⟩,⟨-769852225423,-769631147573⟩⟩⟩
noncomputable def centerBoxes54 := centerStep53.proposed :: centerBoxes53
theorem centerAccepted53 : StepValid centerStep53.shape centerBoxes53 centerStep53.proposed := by
  dsimp only [StepValid,centerStep53]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep54 : Instruction 40 := ⟨.log 0,⟨⟨185841286016,185841561984⟩,⟨-1375985610793,-1375980742057⟩,⟨1425690029174,1425695071946⟩,⟨17565291954628,17565427364449⟩,⟨-8493378926842,-8493214545286⟩,⟨-2498777759663,-2498577820891⟩⟩⟩
noncomputable def centerBoxes55 := centerStep54.proposed :: centerBoxes54
theorem centerAccepted54 : StepValid centerStep54.shape centerBoxes54 centerStep54.proposed := by
  dsimp only [StepValid,centerStep54]
  exact ⟨by decide,by decide,lc16,by decide⟩
noncomputable def centerStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨63924919463,63925028060⟩,⟨-466192649526,-466190907616⟩,⟨483032725988,483034530108⟩,⟨5794275141677,5794320265798⟩,⟨-2714983832475,-2714926711423⟩,⟨-1015106048674,-1015034286231⟩⟩⟩
noncomputable def centerBoxes56 := centerStep55.proposed :: centerBoxes55
theorem centerAccepted55 : StepValid centerStep55.shape centerBoxes55 centerStep55.proposed := by
  dsimp only [StepValid,centerStep55]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380299946090,380299969485⟩,⟨11329084118,11329396612⟩,⟨-11738687337,-11738363646⟩,⟨-229957613974,-229948032662⟩,⟨158334696635,158345345691⟩,⟨-71037008668,-71024738567⟩⟩⟩
noncomputable def centerBoxes57 := centerStep56.proposed :: centerBoxes56
theorem centerAccepted56 : StepValid centerStep56.shape centerBoxes56 centerStep56.proposed := by
  dsimp only [StepValid,centerStep56]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3178874353452,3178874549009⟩,⟨-94700856300,-94698232554⟩,⟨98119342992,98122060753⟩,⟨1927745598122,1927826235771⟩,⟨-1329433048979,-1329343548618⟩,⟨599742990401,599845962699⟩⟩⟩
noncomputable def centerBoxes58 := centerStep57.proposed :: centerBoxes57
theorem centerAccepted57 : StepValid centerStep57.shape centerBoxes57 centerStep57.proposed := by
  dsimp only [StepValid,centerStep57]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨184817769902,184818095245⟩,⟨-1353347855376,-1353342574404⟩,⟨1402234025244,1402239494874⟩,⟨16944612559012,16944751454677⟩,⟨-8009978608325,-8009805028185⟩,⟨-2813764288368,-2813547874536⟩⟩⟩
noncomputable def centerBoxes59 := centerStep58.proposed :: centerBoxes58
theorem centerAccepted58 : StepValid centerStep58.shape centerBoxes58 centerStep58.proposed := by
  dsimp only [StepValid,centerStep58]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨370659055918,370659657229⟩,⟨-2729333466169,-2729323316461⟩,⟨2827924054418,2827934566820⟩,⟨34509904513640,34510178819126⟩,⟨-16503357535167,-16503019573471⟩,⟨-5312542048031,-5312125695427⟩⟩⟩
noncomputable def centerBoxes60 := centerStep59.proposed :: centerBoxes59
theorem centerAccepted59 : StepValid centerStep59.shape centerBoxes59 centerStep59.proposed := by
  dsimp only [StepValid,centerStep59]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨522853714426,522853945911⟩,⟨79617503600,79620956782⟩,⟨-82497377838,-82493801284⟩,⟨-1591483145648,-1591391343481⟩,⟨1087212959330,1087327103154⟩,⟨-472831377743,-472689572555⟩⟩⟩
noncomputable def centerBoxes61 := centerStep60.proposed :: centerBoxes60
theorem centerAccepted60 : StepValid centerStep60.shape centerBoxes60 centerStep60.proposed := by
  dsimp only [StepValid,centerStep60]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨360554054128,360554293573⟩,⟨82355005550,82358595696⟩,⟨-85333917877,-85330199458⟩,⟨-1639933441241,-1639837574746⟩,⟨1118097397629,1118216278042⟩,⟨-482357395382,-482210023000⟩⟩⟩
noncomputable def centerBoxes62 := centerStep61.proposed :: centerBoxes61
theorem centerAccepted61 : StepValid centerStep61.shape centerBoxes61 centerStep61.proposed := by
  dsimp only [StepValid,centerStep61]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨721108108256,721108587146⟩,⟨164710011100,164717191392⟩,⟨-170667835754,-170660398916⟩,⟨-3279866882482,-3279675149492⟩,⟨2236194795258,2236432556084⟩,⟨-964714790764,-964420046000⟩⟩⟩
noncomputable def centerBoxes63 := centerStep62.proposed :: centerBoxes62
theorem centerAccepted62 : StepValid centerStep62.shape centerBoxes62 centerStep62.proposed := by
  dsimp only [StepValid,centerStep62]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1524274653803,1524274738722⟩,⟨-825142022,-824100844⟩,⟨853872832,854951310⟩,⟨28740680880,28772514093⟩,⟨-23996047648,-23960593966⟩,⟨18052770599,18093710352⟩⟩⟩
noncomputable def centerBoxes64 := centerStep63.proposed :: centerBoxes63
theorem centerAccepted63 : StepValid centerStep63.shape centerBoxes63 centerStep63.proposed := by
  dsimp only [StepValid,centerStep63]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨999686391939,999687111528⟩,⟨227799571939,227810222052⟩,⟨-236040192368,-236029161664⟩,⟨-4528342221850,-4528054952433⟩,⟨3084599096966,3084952479086⟩,⟨-1325828827029,-1325392937709⟩⟩⟩
noncomputable def centerBoxes65 := centerStep64.proposed :: centerBoxes64
theorem centerAccepted64 : StepValid centerStep64.shape centerBoxes64 centerStep64.proposed := by
  dsimp only [StepValid,centerStep64]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67746000856,67746003724⟩,⟨14295734820,14295799354⟩,⟨-14812255686,-14812188840⟩,⟨-284824046544,-284822068414⟩,⟨194264567990,194266769278⟩,⟨-83896192253,-83893652651⟩⟩⟩
noncomputable def centerBoxes66 := centerStep65.proposed :: centerBoxes65
theorem centerAccepted65 : StepValid centerStep65.shape centerBoxes65 centerStep65.proposed := by
  dsimp only [StepValid,centerStep65]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50965410652,50965413541⟩,⟨261842346732,261842411757⟩,⟨35746215285,35746268672⟩,⟨-1259874977314,-1259872956503⟩,⟨-204607407323,-204605439971⟩,⟨-167894429079,-167892421100⟩⟩⟩
noncomputable def centerBoxes67 := centerStep66.proposed :: centerBoxes66
theorem centerAccepted66 : StepValid centerStep66.shape centerBoxes66 centerStep66.proposed := by
  dsimp only [StepValid,centerStep66]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2134857366767,2134857539063⟩,⟨-323302553368,-323301080928⟩,⟨334980798366,334982323560⟩,⟨6534015006324,6534060227207⟩,⟨-4489437127108,-4489386934012⟩,⟨1996795261905,1996853013750⟩⟩⟩
noncomputable def centerBoxes68 := centerStep67.proposed :: centerBoxes67
theorem centerAccepted67 : StepValid centerStep67.shape centerBoxes67 centerStep67.proposed := by
  dsimp only [StepValid,centerStep67]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2974769933519,2974770293642⟩,⟨-675748250659,-675745145781⟩,⟨700157412947,700160629073⟩,⟨13708185896894,13708281430070⟩,⟨-9436577285507,-9436471515460⟩,⟨4228516409515,4228637785483⟩⟩⟩
noncomputable def centerBoxes69 := centerStep68.proposed :: centerBoxes68
theorem centerAccepted68 : StepValid centerStep68.shape centerBoxes68 centerStep68.proposed := by
  dsimp only [StepValid,centerStep68]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨137888829392,137888853902⟩,⟨677101480810,677101888196⟩,⟨129166961904,129167268970⟩,⟨-3095078169349,-3095066266329⟩,⟨-846215443170,-846204184813⟩,⟨-212715649106,-212704247114⟩⟩⟩
noncomputable def centerBoxes70 := centerStep69.proposed :: centerBoxes69
theorem centerAccepted69 : StepValid centerStep69.shape centerBoxes69 centerStep69.proposed := by
  dsimp only [StepValid,centerStep69]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8767393341842,8767394900263⟩,⟨-43052215815480,-43052174607412⟩,⟨-8212851325535,-8212828881643⟩,⟨619608063420645,619609624463105⟩,⟨134462225233558,134463243489062⟩,⟨28911068572087,28911879715773⟩⟩⟩
noncomputable def centerBoxes71 := centerStep70.proposed :: centerBoxes70
theorem centerAccepted70 : StepValid centerStep70.shape centerBoxes70 centerStep70.proposed := by
  dsimp only [StepValid,centerStep70]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨7971397114139,7971404269001⟩,⟨-37327060293288,-37326909404659⟩,⟨-9349368336060,-9349254262592⟩,⟨509404813006122,509409786009012⟩,⟨154390861623200,154395222600459⟩,⟨19240243239312,19244651701275⟩⟩⟩
noncomputable def centerBoxes72 := centerStep71.proposed :: centerBoxes71
theorem centerAccepted71 : StepValid centerStep71.shape centerBoxes71 centerStep71.proposed := by
  dsimp only [StepValid,centerStep71]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨15942794228278,15942808538002⟩,⟨-74654120586576,-74653818809318⟩,⟨-18698736672120,-18698508525184⟩,⟨1018809626012244,1018819572018024⟩,⟨308781723246400,308790445200918⟩,⟨38480486478624,38489303402550⟩⟩⟩
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
noncomputable def centerStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7383311431190,7383311431326⟩,⟨-43837227782284,-43837227780622⟩,⟨-19686565955704,-19686565954932⟩,⟨520553022149966,520553022179822⟩,⟨283351203946872,283351203962403⟩,⟨104982942331456,104982942337743⟩⟩⟩
noncomputable def centerBoxes77 := centerStep76.proposed :: centerBoxes76
theorem centerAccepted76 : StepValid centerStep76.shape centerBoxes76 centerStep76.proposed := by
  dsimp only [StepValid,centerStep76]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6283799803414,6283799803550⟩,⟨-43837227782284,-43837227780621⟩,⟨-19686565955705,-19686565954931⟩,⟨520553022149965,520553022179816⟩,⟨283351203946871,283351203962401⟩,⟨104982942331455,104982942337743⟩⟩⟩
noncomputable def centerBoxes78 := centerStep77.proposed :: centerBoxes77
theorem centerAccepted77 : StepValid centerStep77.shape centerBoxes77 centerStep77.proposed := by
  dsimp only [StepValid,centerStep77]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep78 : Instruction 40 := ⟨.log 0,⟨⟨1916568342528,1916568381120⟩,⟨-7670445142118,-7670445141626⟩,⟨-3444668648982,-3444668648756⟩,⟨37573292785860,37573292802300⟩,⟨25548748256823,25548748264837⟩,⟨7577623530887,7577623534306⟩⟩⟩
noncomputable def centerBoxes79 := centerStep78.proposed :: centerBoxes78
theorem centerAccepted78 : StepValid centerStep78.shape centerBoxes78 centerStep78.proposed := by
  dsimp only [StepValid,centerStep78]
  exact ⟨by decide,by decide,lc18,by decide⟩
noncomputable def centerStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨101523589692,101523589694⟩,⟨873166851276,873166851278⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes80 := centerStep79.proposed :: centerBoxes79
theorem centerAccepted79 : StepValid centerStep79.shape centerBoxes79 centerStep79.proposed := by
  dsimp only [StepValid,centerStep79]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨139354057504,139354057508⟩,⟨682618897313,682618897322⟩,⟨306552732104,306552732109⟩,⟨-1719138590394,-1719138590390⟩,⟨-1544072787400,-1544072787390⟩,⟨-346708634503,-346708634500⟩⟩⟩
noncomputable def centerBoxes81 := centerStep80.proposed :: centerBoxes80
theorem centerAccepted80 : StepValid centerStep80.shape centerBoxes80 centerStep80.proposed := by
  dsimp only [StepValid,centerStep80]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4297107919424,4297108015872⟩,⟨-19578276841961,-19578276841065⟩,⟨-3444668648982,-3444668648756⟩,⟨139988149675626,139988149715618⟩,⟨25548748256823,25548748264837⟩,⟨7577623530887,7577623534306⟩⟩⟩
noncomputable def centerBoxes82 := centerStep81.proposed :: centerBoxes81
theorem centerAccepted81 : StepValid centerStep81.shape centerBoxes81 centerStep81.proposed := by
  dsimp only [StepValid,centerStep81]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨741318111836,741319314458⟩,⟨-5458666932338,-5458646632922⟩,⟨5655848108836,5655869133640⟩,⟨69019809027280,69020357638252⟩,⟨-33006715070334,-33006039146942⟩,⟨-10625084096062,-10624251390854⟩⟩⟩
noncomputable def centerBoxes83 := centerStep82.proposed :: centerBoxes82
theorem centerAccepted82 : StepValid centerStep82.shape centerBoxes82 centerStep82.proposed := by
  dsimp only [StepValid,centerStep82]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5038426031260,5038427330330⟩,⟨-25036943774299,-25036923473987⟩,⟨2211179459854,2211200484884⟩,⟨209007958702906,209008507353870⟩,⟨-7457966813511,-7457290882105⟩,⟨-3047460565175,-3046627856548⟩⟩⟩
noncomputable def centerBoxes84 := centerStep83.proposed :: centerBoxes83
theorem centerAccepted83 : StepValid centerStep83.shape centerBoxes83 centerStep83.proposed := by
  dsimp only [StepValid,centerStep83]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨465223908660,465224028620⟩,⟨1689428414618,1689431320751⟩,⟨204169624537,204171565892⟩,⟨-30543778258240,-30543692757243⟩,⟨1067354827537,1067433936626⟩,⟨-281387780004,-281310891707⟩⟩⟩
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
noncomputable def centerStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨36375838934,36375841051⟩,⟨-745459771117,-745459760403⟩,⟨314071324370,314071342618⟩,⟨9224227643244,9224227671569⟩,⟨-6436347433334,-6436347341287⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes92 := centerStep91.proposed :: centerBoxes91
theorem centerAccepted91 : StepValid centerStep91.shape centerBoxes91 centerStep91.proposed := by
  dsimp only [StepValid,centerStep91]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨501599747594,501599869671⟩,⟨943968643501,943971560348⟩,⟨518240948907,518242908510⟩,⟨-21319550614996,-21319465085674⟩,⟨-5368992605797,-5368913404661⟩,⟨-281387780004,-281310891707⟩⟩⟩
noncomputable def centerBoxes93 := centerStep92.proposed :: centerBoxes92
theorem centerAccepted92 : StepValid centerStep92.shape centerBoxes92 centerStep92.proposed := by
  dsimp only [StepValid,centerStep92]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep93 : Instruction 40 := ⟨.inv 17,⟨⟨507836879489,507836891833⟩,⟨2540279524621,2540279648204⟩,⟨0,0⟩,⟨3565745386739,3565748309078⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes94 := centerStep93.proposed :: centerBoxes93
theorem centerAccepted93 : StepValid centerStep93.shape centerBoxes93 centerStep93.proposed := by
  dsimp only [StepValid,centerStep93]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨231676358972,231676420988⟩,⟨1594876865618,1594878561858⟩,⟨239362513017,239363423928⟩,⟨-3858430227123,-3858375064644⟩,⟨-1282474518917,-1282433291958⟩,⟨-129965970334,-129930454396⟩⟩⟩
noncomputable def centerBoxes95 := centerStep94.proposed :: centerBoxes94
theorem centerAccepted94 : StepValid centerStep94.shape centerBoxes94 centerStep94.proposed := by
  dsimp only [StepValid,centerStep94]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-741319314458,-741318111836⟩,⟨5458646632922,5458666932338⟩,⟨-5655869133640,-5655848108836⟩,⟨-69020357638252,-69019809027280⟩,⟨33006039146942,33006715070334⟩,⟨10624251390854,10625084096062⟩⟩⟩
noncomputable def centerBoxes96 := centerStep95.proposed :: centerBoxes95
theorem centerAccepted95 : StepValid centerStep95.shape centerBoxes95 centerStep95.proposed := by
  dsimp only [StepValid,centerStep95]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3555788604966,3555789904036⟩,⟨-14119630209039,-14119609908727⟩,⟨-9100537782622,-9100516757592⟩,⟨70967792037374,70968340688338⟩,⟨58554787403765,58555463335171⟩,⟨18201874921741,18202707630368⟩⟩⟩
noncomputable def centerBoxes97 := centerStep96.proposed :: centerBoxes96
theorem centerAccepted96 : StepValid centerStep96.shape centerBoxes96 centerStep96.proposed := by
  dsimp only [StepValid,centerStep96]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨450666966324,450667130985⟩,⟨418022624633,418026004125⟩,⟨-162035716019,-162032689027⟩,⟨-14097075726234,-14096978951151⟩,⟨-7158779681684,-7158673475195⟩,⟨-3888915106956,-3888797434292⟩⟩⟩
noncomputable def centerBoxes98 := centerStep97.proposed :: centerBoxes97
theorem centerAccepted97 : StepValid centerStep97.shape centerBoxes97 centerStep97.proposed := by
  dsimp only [StepValid,centerStep97]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨327475234076,327475234082⟩,⟨1944331694898,1944331694900⟩,⟨873166851276,873166851278⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes99 := centerStep98.proposed :: centerBoxes98
theorem centerAccepted98 : StepValid centerStep98.shape centerBoxes98 centerStep98.proposed := by
  dsimp only [StepValid,centerStep98]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-327475234082,-327475234076⟩,⟨-1944331694900,-1944331694898⟩,⟨-873166851278,-873166851276⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes100 := centerStep99.proposed :: centerBoxes99
theorem centerAccepted99 : StepValid centerStep99.shape centerBoxes99 centerStep99.proposed := by
  dsimp only [StepValid,centerStep99]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨772036393694,772036393700⟩,⟨-1944331694900,-1944331694898⟩,⟨-873166851278,-873166851276⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes101 := centerStep100.proposed :: centerBoxes100
theorem centerAccepted100 : StepValid centerStep100.shape centerBoxes100 centerStep100.proposed := by
  dsimp only [StepValid,centerStep100]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1345743395571,1345743422680⟩,⟨-8775084510899,-8775084442262⟩,⟨-3940743717843,-3940743687014⟩,⟨53510783497843,53510783511362⟩,⟨33955346851201,33955346934965⟩,⟨10791829571646,10791829574462⟩⟩⟩
noncomputable def centerBoxes102 := centerStep101.proposed :: centerBoxes101
theorem centerAccepted101 : StepValid centerStep101.shape centerBoxes101 centerStep101.proposed := by
  dsimp only [StepValid,centerStep101]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1345743422680,-1345743395571⟩,⟨8775084442262,8775084510899⟩,⟨3940743687014,3940743717843⟩,⟨-53510783511362,-53510783497843⟩,⟨-33955346934965,-33955346851201⟩,⟨-10791829574462,-10791829571646⟩⟩⟩
noncomputable def centerBoxes103 := centerStep102.proposed :: centerBoxes102
theorem centerAccepted102 : StepValid centerStep102.shape centerBoxes102 centerStep102.proposed := by
  dsimp only [StepValid,centerStep102]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-246231794904,-246231767795⟩,⟨8775084442262,8775084510899⟩,⟨3940743687014,3940743717843⟩,⟨-53510783511362,-53510783497843⟩,⟨-33955346934965,-33955346851201⟩,⟨-10791829574462,-10791829571646⟩⟩⟩
noncomputable def centerBoxes104 := centerStep103.proposed :: centerBoxes103
theorem centerAccepted103 : StepValid centerStep103.shape centerBoxes103 centerStep103.proposed := by
  dsimp only [StepValid,centerStep103]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-11323906661,-11323905412⟩,⟨432074311054,432074317384⟩,⟨83458767773,83458779973⟩,⟨-4493563192268,-4493563175533⟩,⟨1712573200699,1712573262624⟩,⟨2633201279748,2633201304408⟩⟩⟩
noncomputable def centerBoxes105 := centerStep104.proposed :: centerBoxes104
theorem centerAccepted104 : StepValid centerStep104.shape centerBoxes104 centerStep104.proposed := by
  dsimp only [StepValid,centerStep104]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨439343059663,439343225573⟩,⟨850096935687,850100321509⟩,⟨-78576948246,-78573909054⟩,⟨-18590638918502,-18590542126684⟩,⟨-5446206480985,-5446100212571⟩,⟨-1255713827208,-1255596129884⟩⟩⟩
noncomputable def centerBoxes106 := centerStep105.proposed :: centerBoxes105
theorem centerAccepted105 : StepValid centerStep105.shape centerBoxes105 centerStep105.proposed := by
  dsimp only [StepValid,centerStep105]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-101523589694,-101523589692⟩,⟨-873166851278,-873166851276⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes107 := centerStep106.proposed :: centerBoxes106
theorem centerAccepted106 : StepValid centerStep106.shape centerBoxes106 centerStep106.proposed := by
  dsimp only [StepValid,centerStep106]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4668948840,4668948842⟩,⟨28397408507,28397408513⟩,⟨40312003485,40312003486⟩,⟨-303391372745,-303391372734⟩,⟨245185044806,245185044811⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes108 := centerStep107.proposed :: centerBoxes107
theorem centerAccepted107 : StepValid centerStep107.shape centerBoxes107 centerStep107.proposed := by
  dsimp only [StepValid,centerStep107]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨10108685724,10108685975⟩,⟨10917663353,10917664886⟩,⟨87279040344,87279042468⟩,⟨-837070349877,-837070333450⟩,⟨94263805138,94263818079⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes109 := centerStep108.proposed :: centerBoxes108
theorem centerAccepted108 : StepValid centerStep108.shape centerBoxes108 centerStep108.proposed := by
  dsimp only [StepValid,centerStep108]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1461530745166,1461530766114⟩,⟨-7200419315299,-7200418945722⟩,⟨-1344646133929,-1344646068076⟩,⟨103971058779694,103971065994440⟩,⟨22017072325356,22017073784928⟩,⟨4890964954404,4890965230808⟩⟩⟩
noncomputable def centerBoxes110 := centerStep109.proposed :: centerBoxes109
theorem centerAccepted109 : StepValid centerStep109.shape centerBoxes109 centerStep109.proposed := by
  dsimp only [StepValid,centerStep109]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨13437015676,13437016203⟩,⟨-51686835915,-51686828626⟩,⟨103653651745,103653657145⟩,⟨-299784771777,-299784616507⟩,⟨-257198721579,-257198638357⟩,⟨-168509019609,-168509000299⟩⟩⟩
noncomputable def centerBoxes111 := centerStep110.proposed :: centerBoxes110
theorem centerAccepted110 : StepValid centerStep110.shape centerBoxes110 centerStep110.proposed := by
  dsimp only [StepValid,centerStep110]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-13437016203,-13437015676⟩,⟨51686828626,51686835915⟩,⟨-103653657145,-103653651745⟩,⟨299784616507,299784771777⟩,⟨257198638357,257198721579⟩,⟨168509000299,168509019609⟩⟩⟩
noncomputable def centerBoxes112 := centerStep111.proposed :: centerBoxes111
theorem centerAccepted111 : StepValid centerStep111.shape centerBoxes111 centerStep111.proposed := by
  dsimp only [StepValid,centerStep111]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-114960605897,-114960605368⟩,⟨-821480022652,-821480015361⟩,⟨-103653657145,-103653651745⟩,⟨2498807872059,2498808027329⟩,⟨257198638357,257198721579⟩,⟨168509000299,168509019609⟩⟩⟩
noncomputable def centerBoxes113 := centerStep112.proposed :: centerBoxes112
theorem centerAccepted112 : StepValid centerStep112.shape centerBoxes112 centerStep112.proposed := by
  dsimp only [StepValid,centerStep112]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨88140692903,88140694686⟩,⟨-574732175293,-574732170770⟩,⟨602596186673,602596202023⟩,⟨3504737642334,3504737643357⟩,⟨-3388355361403,-3388355322115⟩,⟨-2387065442618,-2387065442245⟩⟩⟩
noncomputable def centerBoxes114 := centerStep113.proposed :: centerBoxes113
theorem centerAccepted113 : StepValid centerStep113.shape centerBoxes113 centerStep113.proposed := by
  dsimp only [StepValid,centerStep113]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨117161409960,117161414010⟩,⟨-1341176100093,-1341176041826⟩,⟨693212140859,693212180205⟩,⟨20520917862966,20520919123671⟩,⟨-5982401103681,-5982400491164⟩,⟨-4254828901877,-4254828716084⟩⟩⟩
noncomputable def centerBoxes115 := centerStep114.proposed :: centerBoxes114
theorem centerAccepted114 : StepValid centerStep114.shape centerBoxes114 centerStep114.proposed := by
  dsimp only [StepValid,centerStep114]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-117161414010,-117161409960⟩,⟨1341176041826,1341176100093⟩,⟨-693212180205,-693212140859⟩,⟨-20520919123671,-20520917862966⟩,⟨5982400491164,5982401103681⟩,⟨4254828716084,4254828901877⟩⟩⟩
noncomputable def centerBoxes116 := centerStep115.proposed :: centerBoxes115
theorem centerAccepted115 : StepValid centerStep115.shape centerBoxes115 centerStep115.proposed := by
  dsimp only [StepValid,centerStep115]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨982350213766,982350217816⟩,⟨1341176041826,1341176100093⟩,⟨-693212180205,-693212140859⟩,⟨-20520919123671,-20520917862966⟩,⟨5982400491164,5982401103681⟩,⟨4254828716084,4254828901877⟩⟩⟩
noncomputable def centerBoxes117 := centerStep116.proposed :: centerBoxes116
theorem centerAccepted116 : StepValid centerStep116.shape centerBoxes116 centerStep116.proposed := by
  dsimp only [StepValid,centerStep116]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨124504811700,124504812217⟩,⟨779863642448,779863652361⟩,⟨186028239010,186028245135⟩,⟨-2471502094395,-2471501855826⟩,⟨-677761828390,-677761704352⟩,⟨-157045935884,-157045889092⟩⟩⟩
noncomputable def centerBoxes118 := centerStep117.proposed :: centerBoxes117
theorem centerAccepted117 : StepValid centerStep117.shape centerBoxes117 centerStep117.proposed := by
  dsimp only [StepValid,centerStep117]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨12019828124,12019828235⟩,⟨171781430004,171781432322⟩,⟨21675235172,21675236402⟩,⟨704976502301,704976558968⟩,⟨101102491604,101102518702⟩,⟨-15693912199,-15693905959⟩⟩⟩
noncomputable def centerBoxes119 := centerStep118.proposed :: centerBoxes118
theorem centerAccepted118 : StepValid centerStep118.shape centerBoxes118 centerStep118.proposed := by
  dsimp only [StepValid,centerStep118]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨174286148139,174286306183⟩,⟨1674694689706,1674700265545⟩,⟨109874428004,109877223919⟩,⟨-1967393126055,-1967179686405⟩,⟨448488190717,448626995171⟩,⟨-544128196793,-544022474838⟩⟩⟩
noncomputable def centerBoxes120 := centerStep119.proposed :: centerBoxes119
theorem centerAccepted119 : StepValid centerStep119.shape centerBoxes119 centerStep119.proposed := by
  dsimp only [StepValid,centerStep119]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-174286306183,-174286148139⟩,⟨-1674700265545,-1674694689706⟩,⟨-109877223919,-109874428004⟩,⟨1967179686405,1967393126055⟩,⟨-448626995171,-448488190717⟩,⟨544022474838,544128196793⟩⟩⟩
noncomputable def centerBoxes121 := centerStep120.proposed :: centerBoxes120
theorem centerAccepted120 : StepValid centerStep120.shape centerBoxes120 centerStep120.proposed := by
  dsimp only [StepValid,centerStep120]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨57390052789,57390272849⟩,⟨-79823399927,-79816127848⟩,⟨129485289098,129488995924⟩,⟨-1891250540718,-1890981938589⟩,⟨-1731101514088,-1730921482675⟩,⟨414056504504,414197742397⟩⟩⟩
noncomputable def centerBoxes122 := centerStep121.proposed :: centerBoxes121
theorem centerAccepted121 : StepValid centerStep121.shape centerBoxes121 centerStep121.proposed := by
  dsimp only [StepValid,centerStep121]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨27790024168421,27790049671408⟩,⟨-241350940394648,-241350311908715⟩,⟨-82541282809191,-82540839633633⟩,⟨3362308775850748,3362330848422154⟩,⟨1273022703397977,1273040787244339⟩,⟨294111766445613,294128664857641⟩⟩⟩
noncomputable def centerBoxes123 := centerStep122.proposed :: centerBoxes122
theorem centerAccepted122 : StepValid centerStep122.shape centerBoxes122 centerStep122.proposed := by
  dsimp only [StepValid,centerStep122]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨14098484949,14098485067⟩,⟨176618006580,176618009560⟩,⟨42130360940,42130362504⟩,⟨546557924562,546558009044⟩,⟨110398197466,110398238242⟩,⟨27382213286,27382228180⟩⟩⟩
noncomputable def centerBoxes124 := centerStep123.proposed :: centerBoxes123
theorem centerAccepted123 : StepValid centerStep123.shape centerBoxes123 centerStep123.proposed := by
  dsimp only [StepValid,centerStep123]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨356337511648,356337841644⟩,⟨1369277053868,1369289310475⟩,⟨6454416188,6461124402⟩,⟨-20610539461480,-20610038042945⟩,⟨-3393160738120,-3392829292532⟩,⟨-1862195541466,-1861943621044⟩⟩⟩
noncomputable def centerBoxes125 := centerStep124.proposed :: centerBoxes124
theorem centerAccepted124 : StepValid centerStep124.shape centerBoxes124 centerStep124.proposed := by
  dsimp only [StepValid,centerStep124]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-356337841644,-356337511648⟩,⟨-1369289310475,-1369277053868⟩,⟨-6461124402,-6454416188⟩,⟨20610038042945,20610539461480⟩,⟨3392829292532,3393160738120⟩,⟨1861943621044,1862195541466⟩⟩⟩
noncomputable def centerBoxes126 := centerStep125.proposed :: centerBoxes125
theorem centerAccepted125 : StepValid centerStep125.shape centerBoxes125 centerStep125.proposed := by
  dsimp only [StepValid,centerStep125]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨83005218019,83005713925⟩,⟨-519192374788,-519176732359⟩,⟨-85038072648,-85028325242⟩,⟨2019399124443,2019997334796⟩,⟨-2053377188453,-2052939474451⟩,⟨606229793836,606599411582⟩⟩⟩
noncomputable def centerBoxes127 := centerStep126.proposed :: centerBoxes126
theorem centerAccepted126 : StepValid centerStep126.shape centerBoxes126 centerStep126.proposed := by
  dsimp only [StepValid,centerStep126]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨240877647196,240877647202⟩,⟨1555785748589,1555785748600⟩,⟨306552732104,306552732109⟩,⟨-3918161845946,-3918161845942⟩,⟨-1544072787400,-1544072787390⟩,⟨-346708634503,-346708634500⟩⟩⟩
noncomputable def centerBoxes128 := centerStep127.proposed :: centerBoxes127
theorem centerAccepted127 : StepValid centerStep127.shape centerBoxes127 centerStep127.proposed := by
  dsimp only [StepValid,centerStep127]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1666917277570,-1666915773730⟩,⟨-4105868825339,-4105826439810⟩,⟨452074754691,452100045146⟩,⟨41261141510216,41262668612825⟩,⟨-7548514715012,-7547398683442⟩,⟨1944579761865,1945547315908⟩⟩⟩
noncomputable def centerBoxes129 := centerStep128.proposed :: centerBoxes128
theorem centerAccepted128 : StepValid centerStep128.shape centerBoxes128 centerStep128.proposed := by
  dsimp only [StepValid,centerStep128]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-188755823388,-188755652314⟩,⟨-1647248266961,-1647242383766⟩,⟨-230837225649,-230834097910⟩,⟨2594752337287,2594989223045⟩,⟨-201276305941,-201123675581⟩,⟨611261519082,611379931045⟩⟩⟩
noncomputable def centerBoxes130 := centerStep129.proposed :: centerBoxes129
theorem centerAccepted129 : StepValid centerStep129.shape centerBoxes129 centerStep129.proposed := by
  dsimp only [StepValid,centerStep129]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨52121823808,52121994888⟩,⟨-91462518372,-91456635166⟩,⟨75715506455,75718634199⟩,⟨-1323409508659,-1323172622897⟩,⟨-1745349093341,-1745196462971⟩,⟨264552884579,264671296545⟩⟩⟩
noncomputable def centerBoxes131 := centerStep130.proposed :: centerBoxes130
theorem centerAccepted130 : StepValid centerStep130.shape centerBoxes130 centerStep130.proposed := by
  dsimp only [StepValid,centerStep130]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨4332536121,4332578620⟩,⟨-33125971049,-33124465671⟩,⟨5336547891,5337411930⟩,⟨38004303770,38066201578⟩,⟨-292837523181,-292795030921⟩,⟨42871234666,42904367096⟩⟩⟩
noncomputable def centerBoxes132 := centerStep131.proposed :: centerBoxes131
theorem centerAccepted131 : StepValid centerStep131.shape centerBoxes131 centerStep131.proposed := by
  dsimp only [StepValid,centerStep131]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨2470810174,2470826395⟩,⟨-8671502502,-8670916256⟩,⟨7178514872,7178834976⟩,⟨-110257001380,-110232173119⟩,⟨-178072684310,-178056339796⟩,⟨35509977814,35522148266⟩⟩⟩
noncomputable def centerBoxes133 := centerStep132.proposed :: centerBoxes132
theorem centerAccepted132 : StepValid centerStep132.shape centerBoxes132 centerStep132.proposed := by
  dsimp only [StepValid,centerStep132]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨4306890841,4306919204⟩,⟨-32352423506,-32351288147⟩,⟨4772060610,4772669659⟩,⟨13224931882,13276948047⟩,⟨-275903217380,-275870274146⟩,⟨33944846181,33968179368⟩⟩⟩
noncomputable def centerBoxes134 := centerStep133.proposed :: centerBoxes133
theorem centerAccepted133 : StepValid centerStep133.shape centerBoxes133 centerStep133.proposed := by
  dsimp only [StepValid,centerStep133]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-4306919204,-4306890841⟩,⟨32351288147,32352423506⟩,⟨-4772669659,-4772060610⟩,⟨-13276948047,-13224931882⟩,⟨275870274146,275903217380⟩,⟨-33968179368,-33944846181⟩⟩⟩
noncomputable def centerBoxes135 := centerStep134.proposed :: centerBoxes134
theorem centerAccepted134 : StepValid centerStep134.shape centerBoxes134 centerStep134.proposed := by
  dsimp only [StepValid,centerStep134]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨25616917,25687779⟩,⟨-774682902,-772042165⟩,⟨563878232,565351320⟩,⟨24727355723,24841269696⟩,⟨-16967249035,-16891813541⟩,⟨8903055298,8959520915⟩⟩⟩
noncomputable def centerBoxes136 := centerStep135.proposed :: centerBoxes135
theorem centerAccepted135 : StepValid centerStep135.shape centerBoxes135 centerStep135.proposed := by
  dsimp only [StepValid,centerStep135]
  exact ⟨by decide,by decide⟩
noncomputable def centerProgram : List (Instruction 40) := [centerStep0,centerStep1,centerStep2,centerStep3,centerStep4,centerStep5,centerStep6,centerStep7,centerStep8,centerStep9,centerStep10,centerStep11,centerStep12,centerStep13,centerStep14,centerStep15,centerStep16,centerStep17,centerStep18,centerStep19,centerStep20,centerStep21,centerStep22,centerStep23,centerStep24,centerStep25,centerStep26,centerStep27,centerStep28,centerStep29,centerStep30,centerStep31,centerStep32,centerStep33,centerStep34,centerStep35,centerStep36,centerStep37,centerStep38,centerStep39,centerStep40,centerStep41,centerStep42,centerStep43,centerStep44,centerStep45,centerStep46,centerStep47,centerStep48,centerStep49,centerStep50,centerStep51,centerStep52,centerStep53,centerStep54,centerStep55,centerStep56,centerStep57,centerStep58,centerStep59,centerStep60,centerStep61,centerStep62,centerStep63,centerStep64,centerStep65,centerStep66,centerStep67,centerStep68,centerStep69,centerStep70,centerStep71,centerStep72,centerStep73,centerStep74,centerStep75,centerStep76,centerStep77,centerStep78,centerStep79,centerStep80,centerStep81,centerStep82,centerStep83,centerStep84,centerStep85,centerStep86,centerStep87,centerStep88,centerStep89,centerStep90,centerStep91,centerStep92,centerStep93,centerStep94,centerStep95,centerStep96,centerStep97,centerStep98,centerStep99,centerStep100,centerStep101,centerStep102,centerStep103,centerStep104,centerStep105,centerStep106,centerStep107,centerStep108,centerStep109,centerStep110,centerStep111,centerStep112,centerStep113,centerStep114,centerStep115,centerStep116,centerStep117,centerStep118,centerStep119,centerStep120,centerStep121,centerStep122,centerStep123,centerStep124,centerStep125,centerStep126,centerStep127,centerStep128,centerStep129,centerStep130,centerStep131,centerStep132,centerStep133,centerStep134,centerStep135]
theorem centerAccepted : Accepted centerProgram centerInitial :=
  ⟨centerAccepted0,⟨centerAccepted1,⟨centerAccepted2,⟨centerAccepted3,⟨centerAccepted4,⟨centerAccepted5,⟨centerAccepted6,⟨centerAccepted7,⟨centerAccepted8,⟨centerAccepted9,⟨centerAccepted10,⟨centerAccepted11,⟨centerAccepted12,⟨centerAccepted13,⟨centerAccepted14,⟨centerAccepted15,⟨centerAccepted16,⟨centerAccepted17,⟨centerAccepted18,⟨centerAccepted19,⟨centerAccepted20,⟨centerAccepted21,⟨centerAccepted22,⟨centerAccepted23,⟨centerAccepted24,⟨centerAccepted25,⟨centerAccepted26,⟨centerAccepted27,⟨centerAccepted28,⟨centerAccepted29,⟨centerAccepted30,⟨centerAccepted31,⟨centerAccepted32,⟨centerAccepted33,⟨centerAccepted34,⟨centerAccepted35,⟨centerAccepted36,⟨centerAccepted37,⟨centerAccepted38,⟨centerAccepted39,⟨centerAccepted40,⟨centerAccepted41,⟨centerAccepted42,⟨centerAccepted43,⟨centerAccepted44,⟨centerAccepted45,⟨centerAccepted46,⟨centerAccepted47,⟨centerAccepted48,⟨centerAccepted49,⟨centerAccepted50,⟨centerAccepted51,⟨centerAccepted52,⟨centerAccepted53,⟨centerAccepted54,⟨centerAccepted55,⟨centerAccepted56,⟨centerAccepted57,⟨centerAccepted58,⟨centerAccepted59,⟨centerAccepted60,⟨centerAccepted61,⟨centerAccepted62,⟨centerAccepted63,⟨centerAccepted64,⟨centerAccepted65,⟨centerAccepted66,⟨centerAccepted67,⟨centerAccepted68,⟨centerAccepted69,⟨centerAccepted70,⟨centerAccepted71,⟨centerAccepted72,⟨centerAccepted73,⟨centerAccepted74,⟨centerAccepted75,⟨centerAccepted76,⟨centerAccepted77,⟨centerAccepted78,⟨centerAccepted79,⟨centerAccepted80,⟨centerAccepted81,⟨centerAccepted82,⟨centerAccepted83,⟨centerAccepted84,⟨centerAccepted85,⟨centerAccepted86,⟨centerAccepted87,⟨centerAccepted88,⟨centerAccepted89,⟨centerAccepted90,⟨centerAccepted91,⟨centerAccepted92,⟨centerAccepted93,⟨centerAccepted94,⟨centerAccepted95,⟨centerAccepted96,⟨centerAccepted97,⟨centerAccepted98,⟨centerAccepted99,⟨centerAccepted100,⟨centerAccepted101,⟨centerAccepted102,⟨centerAccepted103,⟨centerAccepted104,⟨centerAccepted105,⟨centerAccepted106,⟨centerAccepted107,⟨centerAccepted108,⟨centerAccepted109,⟨centerAccepted110,⟨centerAccepted111,⟨centerAccepted112,⟨centerAccepted113,⟨centerAccepted114,⟨centerAccepted115,⟨centerAccepted116,⟨centerAccepted117,⟨centerAccepted118,⟨centerAccepted119,⟨centerAccepted120,⟨centerAccepted121,⟨centerAccepted122,⟨centerAccepted123,⟨centerAccepted124,⟨centerAccepted125,⟨centerAccepted126,⟨centerAccepted127,⟨centerAccepted128,⟨centerAccepted129,⟨centerAccepted130,⟨centerAccepted131,⟨centerAccepted132,⟨centerAccepted133,⟨centerAccepted134,⟨centerAccepted135,True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
noncomputable def center_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨57390052789,57390272849⟩,⟨-79823399927,-79816127848⟩,⟨129485289098,129488995924⟩,⟨-1891250540718,-1890981938589⟩,⟨-1731101514088,-1730921482675⟩,⟨414056504504,414197742397⟩⟩
theorem center_m11_eq : (finalBoxes centerProgram centerInitial).getD 14 (zeroBox 40)=center_m11 := rfl
noncomputable def center_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨25616917,25687779⟩,⟨-774682902,-772042165⟩,⟨563878232,565351320⟩,⟨24727355723,24841269696⟩,⟨-16967249035,-16891813541⟩,⟨8903055298,8959520915⟩⟩
theorem center_kdet_eq : (finalBoxes centerProgram centerInitial).getD 0 (zeroBox 40)=center_kdet := rfl
noncomputable def wholeInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨112957639884,113387136615⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨125413045043,129278515610⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
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
noncomputable def wholeStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨49773302251,51357910303⟩,⟨-129278515610,-125413045043⟩,⟨436368677273,436798174004⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes5 := wholeStep4.proposed :: wholeBoxes4
theorem wholeAccepted4 : StepValid wholeStep4.shape wholeBoxes4 wholeStep4.proposed := by
  dsimp only [StepValid,wholeStep4]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨162730942135,164745046918⟩,⟨970233112166,974098582733⟩,⟨436368677273,436798174004⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes6 := wholeStep5.proposed :: wholeBoxes5
theorem wholeAccepted5 : StepValid wholeStep5.shape wholeBoxes5 wholeStep5.proposed := by
  dsimp only [StepValid,wholeStep5]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨49343805520,51787407034⟩,⟨-129278515610,-125413045043⟩,⟨436368677273,436798174004⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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
noncomputable def wholeStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2100642521216,-2087117463040⟩,⟨6475354545929,6581616896353⟩,⟨2912332987453,2951280592417⟩,⟨-39397201335628,-38135309746836⟩,⟨-25095190922865,-24489766418917⟩,⟨-7921750816583,-7714046141527⟩⟩⟩
noncomputable def wholeBoxes16 := wholeStep15.proposed :: wholeBoxes15
theorem wholeAccepted15 : StepValid wholeStep15.shape wholeBoxes15 wholeStep15.proposed := by
  dsimp only [StepValid,wholeStep15]
  exact ⟨by decide,by decide,lc21,by decide⟩
noncomputable def wholeStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-314749241367,-308899499129⟩,⟨-902666540087,-855563200489⟩,⟨-403479249729,-386120361320⟩,⟨5524919292360,6017664871202⟩,⟨3466798543107,3705385643575⟩,⟨1124710776889,1203183229518⟩⟩⟩
noncomputable def wholeBoxes17 := wholeStep16.proposed :: wholeBoxes16
theorem wholeAccepted16 : StepValid wholeStep16.shape wholeBoxes16 wholeStep16.proposed := by
  dsimp only [StepValid,wholeStep16]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep17 : Instruction 40 := ⟨.neg 0,⟨⟨308899499129,314749241367⟩,⟨855563200489,902666540087⟩,⟨386120361320,403479249729⟩,⟨-6017664871202,-5524919292360⟩,⟨-3705385643575,-3466798543107⟩,⟨-1203183229518,-1124710776889⟩⟩⟩
noncomputable def wholeBoxes18 := wholeStep17.proposed :: wholeBoxes17
theorem wholeAccepted17 : StepValid wholeStep17.shape wholeBoxes17 wholeStep17.proposed := by
  dsimp only [StepValid,wholeStep17]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-164745046918,-162730942135⟩,⟨-974098582733,-970233112166⟩,⟨-436798174004,-436368677273⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes19 := wholeStep18.proposed :: wholeBoxes18
theorem wholeAccepted18 : StepValid wholeStep18.shape wholeBoxes18 wholeStep18.proposed := by
  dsimp only [StepValid,wholeStep18]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨934766580858,936780685641⟩,⟨-974098582733,-970233112166⟩,⟨-436798174004,-436368677273⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes20 := wholeStep19.proposed :: wholeBoxes19
theorem wholeAccepted19 : StepValid wholeStep19.shape wholeBoxes19 wholeStep19.proposed := by
  dsimp only [StepValid,wholeStep19]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep20 : Instruction 40 := ⟨.log 0,⟨⟨-178477712064,-176111186176⟩,⟨-1145775576758,-1138775174201⟩,⟨-513780318150,-512171570158⟩,⟨-1193986165430,-1179440821375⟩,⟨755112484611,762830445806⟩,⟨-240079512258,-238578393034⟩⟩⟩
noncomputable def wholeBoxes21 := wholeStep20.proposed :: wholeBoxes20
theorem wholeAccepted20 : StepValid wholeStep20.shape wholeBoxes20 wholeStep20.proposed := by
  dsimp only [StepValid,wholeStep20]
  exact ⟨by decide,by decide,lc22,by decide⟩
noncomputable def wholeStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-152062487795,-149723611095⟩,⟨-820793071522,-810026985693⟩,⟨-367845198836,-364527412529⟩,⟨992487533900,1027451496139⟩,⟨1367395478740,1384172620021⟩,⟨201989142725,205383458608⟩⟩⟩
noncomputable def wholeBoxes22 := wholeStep21.proposed :: wholeBoxes21
theorem wholeAccepted21 : StepValid wholeStep21.shape wholeBoxes21 wholeStep21.proposed := by
  dsimp only [StepValid,wholeStep21]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep22 : Instruction 40 := ⟨.neg 0,⟨⟨149723611095,152062487795⟩,⟨810026985693,820793071522⟩,⟨364527412529,367845198836⟩,⟨-1027451496139,-992487533900⟩,⟨-1384172620021,-1367395478740⟩,⟨-205383458608,-201989142725⟩⟩⟩
noncomputable def wholeBoxes23 := wholeStep22.proposed :: wholeBoxes22
theorem wholeAccepted22 : StepValid wholeStep22.shape wholeBoxes22 wholeStep22.proposed := by
  dsimp only [StepValid,wholeStep22]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨458623110224,466811729162⟩,⟨1665590186182,1723459611609⟩,⟨750647773849,771324448565⟩,⟨-7045116367341,-6517406826260⟩,⟨-5089558263596,-4834194021847⟩,⟨-1408566688126,-1326699919614⟩⟩⟩
noncomputable def wholeBoxes24 := wholeStep23.proposed :: wholeBoxes23
theorem wholeAccepted23 : StepValid wholeStep23.shape wholeBoxes23 wholeStep23.proposed := by
  dsimp only [StepValid,wholeStep23]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨822140976972,832211799768⟩,⟨4039146640091,4110970648905⟩,⟨750647773849,771324448565⟩,⟨-19055516229668,-18322439237495⟩,⟨-5089558263596,-4834194021847⟩,⟨-1408566688126,-1326699919614⟩⟩⟩
noncomputable def wholeBoxes25 := wholeStep24.proposed :: wholeBoxes24
theorem wholeAccepted24 : StepValid wholeStep24.shape wholeBoxes24 wholeStep24.proposed := by
  dsimp only [StepValid,wholeStep24]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨98687611040,103574814068⟩,⟨-258557031220,-250826090086⟩,⟨872737354546,873596348008⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes26 := wholeStep25.proposed :: wholeBoxes25
theorem wholeAccepted25 : StepValid wholeStep25.shape wholeBoxes25 wholeStep25.proposed := by
  dsimp only [StepValid,wholeStep25]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep26 : Instruction 40 := ⟨.inv 0,⟨⟨11672005694559,12250026187428⟩,⟨28265979313325,32094508824468⟩,⟨-108438921842000,-98350119802552⟩,⟨136902878125531,168172293009615⟩,⟨-320398714348667,-203383736181395⟩,⟨1657426550037652,1919832593063889⟩⟩⟩
noncomputable def wholeBoxes27 := wholeStep26.proposed :: wholeBoxes26
theorem wholeAccepted26 : StepValid wholeStep26.shape wholeBoxes26 wholeStep26.proposed := by
  dsimp only [StepValid,wholeStep26]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨8727542231051,9271949548424⟩,⟨64013477123833,70093780829043⟩,⟨-74107979544405,-64946033386020⟩,⟨97737723889263,172780818552576⟩,⟨-685357229637801,-542177186023778⟩,⟨1071475818303475,1304733351876280⟩⟩⟩
noncomputable def wholeBoxes28 := wholeStep27.proposed :: wholeBoxes27
theorem wholeAccepted27 : StepValid wholeStep27.shape wholeBoxes27 wholeStep27.proposed := by
  dsimp only [StepValid,wholeStep27]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep28 : Instruction 40 := ⟨.contact 0,⟨⟨89939427328,95490700544⟩,⟨-759063973636,-614583779470⟩,⟨623537112080,802534786479⟩,⟨6473279297659,11080698200691⟩,⟨-7502021072701,-1044016423219⟩,⟨-5540037663623,3148043141061⟩⟩⟩
noncomputable def wholeBoxes29 := wholeStep28.proposed :: wholeBoxes28
theorem wholeAccepted28 : StepValid wholeStep28.shape wholeBoxes28 wholeStep28.proposed := by
  dsimp only [StepValid,wholeStep28]
  exact ⟨by decide,by decide,(⟨⟨89939427328,95490700544⟩,⟨-11906900375,-10556245999⟩,⟨2461785876,2957408433⟩⟩ : DyadicJetEnclosure 40),brwhole28_jet,by decide⟩
noncomputable def wholeStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes30 := wholeStep29.proposed :: wholeBoxes29
theorem wholeAccepted29 : StepValid wholeStep29.shape wholeBoxes29 wholeStep29.proposed := by
  dsimp only [StepValid,wholeStep29]
  exact ⟨by decide,by decide,lc4,by decide⟩
noncomputable def wholeStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1189451055104,1195002328320⟩,⟨-759063973636,-614583779470⟩,⟨623537112080,802534786479⟩,⟨6473279297659,11080698200691⟩,⟨-7502021072701,-1044016423219⟩,⟨-5540037663623,3148043141061⟩⟩⟩
noncomputable def wholeBoxes31 := wholeStep30.proposed :: wholeBoxes30
theorem wholeAccepted30 : StepValid wholeStep30.shape wholeBoxes30 wholeStep30.proposed := by
  dsimp only [StepValid,wholeStep30]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep31 : Instruction 40 := ⟨.log 0,⟨⟨86449976896,91569557440⟩,⟨-701667934682,-565473385076⟩,⟨573711271378,741851735423⟩,⟨5508231330621,9952019561236⟩,⟨-6639704649601,-487168233214⟩,⟨-5621666923468,2610650987865⟩⟩⟩
noncomputable def wholeBoxes32 := wholeStep31.proposed :: wholeBoxes31
theorem wholeAccepted31 : StepValid wholeStep31.shape wholeBoxes31 wholeStep31.proposed := by
  dsimp only [StepValid,wholeStep31]
  exact ⟨by decide,by decide,lc32,by decide⟩
noncomputable def wholeStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨93521535957,99522216573⟩,⟨-825822978902,-660050925987⟩,⟨669666629617,873117011295⟩,⟨7099923053889,12707971908525⟩,⟨-8865431589078,-1250469038178⟩,⟨-5920577060350,4182513816280⟩⟩⟩
noncomputable def wholeBoxes33 := wholeStep32.proposed :: wholeBoxes32
theorem wholeAccepted32 : StepValid wholeStep32.shape wholeBoxes32 wholeStep32.proposed := by
  dsimp only [StepValid,wholeStep32]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-95490700544,-89939427328⟩,⟨614583779470,759063973636⟩,⟨-802534786479,-623537112080⟩,⟨-11080698200691,-6473279297659⟩,⟨1044016423219,7502021072701⟩,⟨-3148043141061,5540037663623⟩⟩⟩
noncomputable def wholeBoxes34 := wholeStep33.proposed :: wholeBoxes33
theorem wholeAccepted33 : StepValid wholeStep33.shape wholeBoxes33 wholeStep33.proposed := by
  dsimp only [StepValid,wholeStep33]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1004020927232,1009572200448⟩,⟨614583779470,759063973636⟩,⟨-802534786479,-623537112080⟩,⟨-11080698200691,-6473279297659⟩,⟨1044016423219,7502021072701⟩,⟨-3148043141061,5540037663623⟩⟩⟩
noncomputable def wholeBoxes35 := wholeStep34.proposed :: wholeBoxes34
theorem wholeAccepted34 : StepValid wholeStep34.shape wholeBoxes34 wholeStep34.proposed := by
  dsimp only [StepValid,wholeStep34]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep35 : Instruction 40 := ⟨.log 0,⟨⟨-99894195520,-93831694720⟩,⟨669335002954,831257240365⟩,⟨-878862487321,-679085958168⟩,⟨-12763014785817,-7457424332920⟩,⟨1550422457134,8879966553833⟩,⟨-4149941145584,5647520580867⟩⟩⟩
noncomputable def wholeBoxes36 := wholeStep35.proposed :: wholeBoxes35
theorem wholeAccepted35 : StepValid wholeStep35.shape wholeBoxes35 wholeStep35.proposed := by
  dsimp only [StepValid,wholeStep35]
  exact ⟨by decide,by decide,lc33,by decide⟩
noncomputable def wholeStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-91722907003,-85682572841⟩,⟨542240982485,710812640791⟩,⟨-753759733261,-547195619690⟩,⟨-10418317545446,-4655301211616⟩,⟨-479283217493,7305329849116⟩,⟨-3543584375817,6754531981782⟩⟩⟩
noncomputable def wholeBoxes37 := wholeStep36.proposed :: wholeBoxes36
theorem wholeAccepted36 : StepValid wholeStep36.shape wholeBoxes36 wholeStep36.proposed := by
  dsimp only [StepValid,wholeStep36]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨1798628954,13839643732⟩,⟨-283581996417,50761714804⟩,⟨-84093103644,325921391605⟩,⟨-3318394491557,8052670696909⟩,⟨-9344714806571,6054860810938⟩,⟨-9464161436167,10937045798062⟩⟩⟩
noncomputable def wholeBoxes38 := wholeStep37.proposed :: wholeBoxes37
theorem wholeAccepted37 : StepValid wholeStep37.shape wholeBoxes37 wholeStep37.proposed := by
  dsimp only [StepValid,wholeStep37]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨899314477,6919821866⟩,⟨-141790998209,25380857402⟩,⟨-42046551822,162960695803⟩,⟨-1659197245779,4026335348455⟩,⟨-4672357403286,3027430405469⟩,⟨-4732080718084,5468522899031⟩⟩⟩
noncomputable def wholeBoxes39 := wholeStep38.proposed :: wholeBoxes38
theorem wholeAccepted38 : StepValid wholeStep38.shape wholeBoxes38 wholeStep38.proposed := by
  dsimp only [StepValid,wholeStep38]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-6919821866,-899314477⟩,⟨-25380857402,141790998209⟩,⟨-162960695803,42046551822⟩,⟨-4026335348455,1659197245779⟩,⟨-3027430405469,4672357403286⟩,⟨-5468522899031,4732080718084⟩⟩⟩
noncomputable def wholeBoxes40 := wholeStep39.proposed :: wholeBoxes39
theorem wholeAccepted39 : StepValid wholeStep39.shape wholeBoxes39 wholeStep39.proposed := by
  dsimp only [StepValid,wholeStep39]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨755203561750,761224088403⟩,⟨-25380857402,141790998209⟩,⟨-162960695803,42046551822⟩,⟨-4026335348455,1659197245779⟩,⟨-3027430405469,4672357403286⟩,⟨-5468522899031,4732080718084⟩⟩⟩
noncomputable def wholeBoxes41 := wholeStep40.proposed :: wholeBoxes40
theorem wholeAccepted40 : StepValid wholeStep40.shape wholeBoxes40 wholeStep40.proposed := by
  dsimp only [StepValid,wholeStep40]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨7356994126,8293203692⟩,⟨-131846810474,-100545208934⟩,⟨102009963990,139397541666⟩,⟨1746077496050,2972741185247⟩,⟨-2411158660352,-867865372504⟩,⟨-255065146848,1718346408583⟩⟩⟩
noncomputable def wholeBoxes42 := wholeStep41.proposed :: wholeBoxes41
theorem wholeAccepted41 : StepValid wholeStep41.shape wholeBoxes41 wholeStep41.proposed := by
  dsimp only [StepValid,wholeStep41]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-8293203692,-7356994126⟩,⟨100545208934,131846810474⟩,⟨-139397541666,-102009963990⟩,⟨-2972741185247,-1746077496050⟩,⟨867865372504,2411158660352⟩,⟨-1718346408583,255065146848⟩⟩⟩
noncomputable def wholeBoxes43 := wholeStep42.proposed :: wholeBoxes42
theorem wholeAccepted42 : StepValid wholeStep42.shape wholeBoxes42 wholeStep42.proposed := by
  dsimp only [StepValid,wholeStep42]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1091218424084,1092154633650⟩,⟨100545208934,131846810474⟩,⟨-139397541666,-102009963990⟩,⟨-2972741185247,-1746077496050⟩,⟨867865372504,2411158660352⟩,⟨-1718346408583,255065146848⟩⟩⟩
noncomputable def wholeBoxes44 := wholeStep43.proposed :: wholeBoxes43
theorem wholeAccepted43 : StepValid wholeStep43.shape wholeBoxes43 wholeStep43.proposed := by
  dsimp only [StepValid,wholeStep43]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep44 : Instruction 40 := ⟨.log 0,⟨⟨-8324638144,-7381717824⟩,⟨101222503603,132848839428⟩,⟨-140456955787,-102697125571⟩,⟨-3011385367747,-1767158136963⟩,⟨883165938814,2446454097713⟩,⟨-1749348406332,247411461390⟩⟩⟩
noncomputable def wholeBoxes45 := wholeStep44.proposed :: wholeBoxes44
theorem wholeAccepted44 : StepValid wholeStep44.shape wholeBoxes44 wholeStep44.proposed := by
  dsimp only [StepValid,wholeStep44]
  exact ⟨by decide,by decide,lc30,by decide⟩
noncomputable def wholeStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-4162319072,-3690858912⟩,⟨50611251801,66424419714⟩,⟨-70228477894,-51348562785⟩,⟨-1505692683874,-883579068481⟩,⟨441582969407,1223227048857⟩,⟨-874674203166,123705730695⟩⟩⟩
noncomputable def wholeBoxes46 := wholeStep45.proposed :: wholeBoxes45
theorem wholeAccepted45 : StepValid wholeStep45.shape wholeBoxes45 wholeStep45.proposed := by
  dsimp only [StepValid,wholeStep45]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3690858912,4162319072⟩,⟨-66424419714,-50611251801⟩,⟨51348562785,70228477894⟩,⟨883579068481,1505692683874⟩,⟨-1223227048857,-441582969407⟩,⟨-123705730695,874674203166⟩⟩⟩
noncomputable def wholeBoxes47 := wholeStep46.proposed :: wholeBoxes46
theorem wholeAccepted46 : StepValid wholeStep46.shape wholeBoxes46 wholeStep46.proposed := by
  dsimp only [StepValid,wholeStep46]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765814242528,766285721952⟩,⟨-66424419714,-50611251801⟩,⟨51348562785,70228477894⟩,⟨883579068481,1505692683874⟩,⟨-1223227048857,-441582969407⟩,⟨-123705730695,874674203166⟩⟩⟩
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
noncomputable def wholeStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272804606021,273038658413⟩,⟨25136302233,32961702619⟩,⟨-34849385417,-25502490997⟩,⟨-743185296312,-436519374012⟩,⟨216966343126,602789665088⟩,⟨-429586602146,63766286712⟩⟩⟩
noncomputable def wholeBoxes51 := wholeStep50.proposed :: wholeBoxes50
theorem wholeAccepted50 : StepValid wholeStep50.shape wholeBoxes50 wholeStep50.proposed := by
  dsimp only [StepValid,wholeStep50]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1531628485056,1532571443904⟩,⟨-132848839428,-101222503602⟩,⟨102697125570,140456955788⟩,⟨1767158136962,3011385367748⟩,⟨-2446454097714,-883165938814⟩,⟨-247411461390,1749348406332⟩⟩⟩
noncomputable def wholeBoxes52 := wholeStep51.proposed :: wholeBoxes51
theorem wholeAccepted51 : StepValid wholeStep51.shape wholeBoxes51 wholeStep51.proposed := by
  dsimp only [StepValid,wholeStep51]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1197463459352,1204084284327⟩,⟨-910316684310,-728963830718⟩,⟨739583466079,962449584284⟩,⟨8565543018757,14665104444336⟩,⟨-10452159911660,-2138770778792⟩,⟨-5730386819763,5313940846322⟩⟩⟩
noncomputable def wholeBoxes53 := wholeStep52.proposed :: wholeBoxes52
theorem wholeAccepted52 : StepValid wholeStep52.shape wholeBoxes52 wholeStep52.proposed := by
  dsimp only [StepValid,wholeStep52]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1295415290928,1308656940878⟩,⟨-1820633368619,-1457927661436⟩,⟨1479166932158,1924899168567⟩,⟨17131086037519,29330208888660⟩,⟨-20904319823312,-4277541557585⟩,⟨-11456161155346,10627881692641⟩⟩⟩
noncomputable def wholeBoxes54 := wholeStep53.proposed :: wholeBoxes53
theorem wholeAccepted53 : StepValid wholeStep53.shape wholeBoxes53 wholeStep53.proposed := by
  dsimp only [StepValid,wholeStep53]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep54 : Instruction 40 := ⟨.log 0,⟨⟨180281671680,191463752960⟩,⟨-1545301782937,-1224926385312⟩,⟨1242771264589,1633799626234⟩,⟨12221416574888,23530000025471⟩,⟨-16358464872699,-1297705192918⟩,⟨-12151378829911,7615946725879⟩⟩⟩
noncomputable def wholeBoxes55 := wholeStep54.proposed :: wholeBoxes54
theorem wholeAccepted54 : StepValid wholeStep54.shape wholeBoxes54 wholeStep54.proposed := by
  dsimp only [StepValid,wholeStep54]
  exact ⟨by decide,by decide,lc35,by decide⟩
noncomputable def wholeStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨61775222875,66111007503⟩,⟨-527726494715,-409814799695⟩,⟨414125876816,559269998065⟩,⟨3900740122564,7850634286095⟩,⟨-5504348924837,-95304529106⟩,⟨-4548352496569,2651835178847⟩⟩⟩
noncomputable def wholeBoxes56 := wholeStep55.proposed :: wholeBoxes55
theorem wholeAccepted55 : StepValid wholeStep55.shape wholeBoxes55 wholeStep55.proposed := by
  dsimp only [StepValid,wholeStep55]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380018996507,380579195704⟩,⟨2025087833,20829428615⟩,⟨-23094729884,-645889373⟩,⟨-605408359848,135105796629⟩,⟨-300589691784,629503021830⟩,⟨-669128648772,518528456289⟩⟩⟩
noncomputable def wholeBoxes57 := wholeStep56.proposed :: wholeBoxes56
theorem wholeAccepted56 : StepValid wholeStep56.shape wholeBoxes56 wholeStep56.proposed := by
  dsimp only [StepValid,wholeStep56]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3176542052905,3181224703835⟩,⟨-174367843413,-16902596713⟩,⟨5390979796,193331191101⟩,⟨-1130821206573,5087124625666⟩,⟨-5290905294614,2516246713284⟩,⟨-4340700323531,5624925254892⟩⟩⟩
noncomputable def wholeBoxes58 := wholeStep57.proposed :: wholeBoxes57
theorem wholeAccepted57 : StepValid wholeStep57.shape wholeBoxes57 wholeStep57.proposed := by
  dsimp only [StepValid,wholeStep57]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨178471594417,191279441664⟩,⟨-1537359090126,-1184924355413⟩,⟨1196732493445,1629764350386⟩,⟨11214032543718,23187552622028⟩,⟨-16425385686579,-132419104541⟩,⟨-13416715143670,8207463658368⟩⟩⟩
noncomputable def wholeBoxes59 := wholeStep58.proposed :: wholeBoxes58
theorem wholeAccepted58 : StepValid wholeStep58.shape wholeBoxes58 wholeStep58.proposed := by
  dsimp only [StepValid,wholeStep58]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨358753266097,382743194624⟩,⟨-3082660873063,-2409850740725⟩,⟨2439503758034,3263563976620⟩,⟨23435449118606,46717552647499⟩,⟨-32783850559278,-1430124297459⟩,⟨-25568093973581,15823410384247⟩⟩⟩
noncomputable def wholeBoxes60 := wholeStep59.proposed :: wholeBoxes59
theorem wholeAccepted59 : StepValid wholeStep59.shape wholeBoxes59 wholeStep59.proposed := by
  dsimp only [StepValid,wholeStep59]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨518714313948,527017721438⟩,⟨-35143821222,196332118060⟩,⟨-225644920844,58220117502⟩,⟨-5581645804959,2333991866312⟩,⟨-4233987620562,6480464121640⟩,⟨-7584500588688,6600621453346⟩⟩⟩
noncomputable def wholeBoxes61 := wholeStep60.proposed :: wholeBoxes60
theorem wholeAccepted60 : StepValid wholeStep60.shape wholeBoxes60 wholeStep60.proposed := by
  dsimp only [StepValid,wholeStep60]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨356280813706,364869797135⟩,⟨-36496644416,203889709512⟩,⟨-234330876774,60461237634⟩,⟨-5803303316263,2461814289437⟩,⟨-4440618502496,6741184482054⟩,⟨-7889401064142,6904870090725⟩⟩⟩
noncomputable def wholeBoxes62 := wholeStep61.proposed :: wholeBoxes61
theorem wholeAccepted61 : StepValid wholeStep61.shape wholeBoxes61 wholeStep61.proposed := by
  dsimp only [StepValid,wholeStep61]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨712561627412,729739594270⟩,⟨-72993288832,407779419024⟩,⟨-468661753548,120922475268⟩,⟨-11606606632526,4923628578874⟩,⟨-8881237004992,13482368964108⟩,⟨-15778802128284,13809740181450⟩⟩⟩
noncomputable def wholeBoxes63 := wholeStep62.proposed :: wholeBoxes62
theorem wholeAccepted62 : StepValid wholeStep62.shape wholeBoxes62 wholeStep62.proposed := by
  dsimp only [StepValid,wholeStep62]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1523335281364,1525214449778⟩,⟨-32303630494,30624306872⟩,⟨-36700416096,38446991798⟩,⟨-1205583048285,1265307871698⟩,⟨-1578588725210,1527992721538⟩,⟨-1965757869973,2004413553180⟩⟩⟩
noncomputable def wholeBoxes64 := wholeStep63.proposed :: wholeBoxes63
theorem wholeAccepted63 : StepValid wholeStep63.shape wholeBoxes63 wholeStep63.proposed := by
  dsimp only [StepValid,wholeStep63]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨987229456934,1012276128455⟩,⟨-122694161359,585986373598⟩,⟨-674473472211,193257618574⟩,⟨-16924487995024,7692424906862⟩,⟨-13394190158112,19744546187260⟩,⟨-23225389328131,20518123499826⟩⟩⟩
noncomputable def wholeBoxes65 := wholeStep64.proposed :: wholeBoxes64
theorem wholeAccepted64 : StepValid wholeStep64.shape wholeBoxes64 wholeStep64.proposed := by
  dsimp only [StepValid,wholeStep64]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67686735807,67802929142⟩,⟨12473354266,16370575508⟩,⟨-17308101526,-12655067636⟩,⟨-367956968272,-214637151670⟩,⟨105575459524,298212113450⟩,⟨-212173058528,33878934192⟩⟩⟩
noncomputable def wholeBoxes66 := wholeStep65.proposed :: wholeBoxes65
theorem wholeAccepted65 : StepValid wholeStep65.shape wholeBoxes65 wholeStep65.proposed := by
  dsimp only [StepValid,wholeStep65]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50611596729,51319509740⟩,⟨257979542926,265899541519⟩,⟨33110055693,38102195743⟩,⟨-1361945154295,-1166017855882⟩,⟨-291110198873,-106887294117⟩,⟨-271737184429,-73309397387⟩⟩⟩
noncomputable def wholeBoxes67 := wholeStep66.proposed :: wholeBoxes66
theorem wholeAccepted66 : StepValid wholeStep66.shape wholeBoxes66 wholeStep66.proposed := by
  dsimp only [StepValid,wholeStep66]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2133570720829,2136198627950⟩,⟨-370346856768,-282007513024⟩,⟨286115833398,391556240246⟩,⟨4941968173452,8427036000902⟩,⟨-6853997970294,-2479423290570⟩,⟨-670532319457,4912598468607⟩⟩⟩
noncomputable def wholeBoxes68 := wholeStep67.proposed :: wholeBoxes67
theorem wholeAccepted67 : StepValid wholeStep67.shape wholeBoxes67 wholeStep67.proposed := by
  dsimp only [StepValid,wholeStep67]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2972081066130,2977573800039⟩,⟨-774320620198,-589258079271⟩,⟨597842463945,818665165502⟩,⟨10365244724926,17686354406361⟩,⟨-14401292934877,-5220294996422⟩,⟨-1361870237848,10346282023254⟩⟩⟩
noncomputable def wholeBoxes69 := wholeStep68.proposed :: wholeBoxes68
theorem wholeAccepted68 : StepValid wholeStep68.shape wholeBoxes68 wholeStep68.proposed := by
  dsimp only [StepValid,wholeStep68]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨136807801359,138977727723⟩,⟨661201156952,692955123662⟩,⟨117018800042,141395134692⟩,⟨-3585658867727,-2602862527896⟩,⟨-1347090423568,-348984798506⟩,⟨-763446986853,341488457608⟩⟩⟩
noncomputable def wholeBoxes70 := wholeStep69.proposed :: wholeBoxes69
theorem wholeAccepted69 : StepValid wholeStep69.shape wholeBoxes69 wholeStep69.proposed := by
  dsimp only [StepValid,wholeStep69]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8698701866993,8836673110785⟩,⟨-44759274306123,-41384989038670⟩,⟨-9132977595700,-7324279012730⟩,⟨556701650431086,685031345388057⟩,⟨91535229715247,179531318522910⟩,⟨-9723342756775,68190911352489⟩⟩⟩
noncomputable def wholeBoxes71 := wholeStep70.proposed :: wholeBoxes70
theorem wholeAccepted70 : StepValid wholeStep70.shape wholeBoxes70 wholeStep70.proposed := by
  dsimp only [StepValid,wholeStep70]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨7810390088872,8135569482882⟩,⟨-42194145047315,-32449234116034⟩,⟨-13829045926893,-5023129770654⟩,⟨316121668564722,702493458228673⟩,⟨-38194844884654,352448182284313⟩,⟨-198822741482353,238887773025989⟩⟩⟩
noncomputable def wholeBoxes72 := wholeStep71.proposed :: wholeBoxes71
theorem wholeAccepted71 : StepValid wholeStep71.shape wholeBoxes71 wholeStep71.proposed := by
  dsimp only [StepValid,wholeStep71]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨15620780177744,16271138965764⟩,⟨-84388290094630,-64898468232068⟩,⟨-27658091853786,-10046259541308⟩,⟨632243337129444,1404986916457346⟩,⟨-76389689769308,704896364568626⟩,⟨-397645482964706,477775546051978⟩⟩⟩
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
noncomputable def wholeStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7338161858161,7428985562019⟩,⟨-44469504153080,-43216641412989⟩,⟨-19940690354390,-19436966655845⟩,⟨509031588869024,532384074006271⟩,⟨277915314877259,288922633993438⟩,⟨102967386133704,107048567665158⟩⟩⟩
noncomputable def wholeBoxes77 := wholeStep76.proposed :: wholeBoxes76
theorem wholeAccepted76 : StepValid wholeStep76.shape wholeBoxes76 wholeStep76.proposed := by
  dsimp only [StepValid,wholeStep76]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6238650230385,6329473934243⟩,⟨-44469504153081,-43216641412988⟩,⟨-19940690354390,-19436966655844⟩,⟨509031588869024,532384074006271⟩,⟨277915314877258,288922633993439⟩,⟨102967386133703,107048567665159⟩⟩⟩
noncomputable def wholeBoxes78 := wholeStep77.proposed :: wholeBoxes77
theorem wholeAccepted77 : StepValid wholeStep77.shape wholeBoxes77 wholeStep77.proposed := by
  dsimp only [StepValid,wholeStep77]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep78 : Instruction 40 := ⟨.log 0,⟨⟨1908639750976,1924531334848⟩,⟨-7837390315590,-7507290533220⟩,⟨-3514385339933,-3376452935699⟩,⟨32559954710223,42569799825489⟩,⟨23226723871774,27866392973303⟩,⟨6653686989633,8497809239433⟩⟩⟩
noncomputable def wholeBoxes79 := wholeStep78.proposed :: wholeBoxes78
theorem wholeAccepted78 : StepValid wholeStep78.shape wholeBoxes78 wholeStep78.proposed := by
  dsimp only [StepValid,wholeStep78]
  exact ⟨by decide,by decide,lc37,by decide⟩
noncomputable def wholeStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨101308883270,101738380002⟩,⟨872737354546,873596348008⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes80 := wholeStep79.proposed :: wholeBoxes79
theorem wholeAccepted79 : StepValid wholeStep79.shape wholeBoxes79 wholeStep79.proposed := by
  dsimp only [StepValid,wholeStep79]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨138348192539,140362297323⟩,⟨678904663963,686331795607⟩,⟨305537942747,307566921911⟩,⟨-1725980926281,-1712309844048⟩,⟨-1548001508070,-1540144066720⟩,⟨-347049799190,-346367637584⟩⟩⟩
noncomputable def wholeBoxes81 := wholeStep80.proposed :: wholeBoxes80
theorem wholeAccepted80 : StepValid wholeStep80.shape wholeBoxes80 wholeStep80.proposed := by
  dsimp only [StepValid,wholeStep80]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4286855530432,4307398673920⟩,⟨-19815831460907,-19344972193802⟩,⟨-3514385339933,-3376452935699⟩,⟨131642159561890,148314130577590⟩,⟨23226723871774,27866392973303⟩,⟨6653686989633,8497809239433⟩⟩⟩
noncomputable def wholeBoxes82 := wholeStep81.proposed :: wholeBoxes81
theorem wholeAccepted81 : StepValid wholeStep81.shape wholeBoxes81 wholeStep81.proposed := by
  dsimp only [StepValid,wholeStep81]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨717506532194,765486389248⟩,⟨-6165321746126,-4819701481450⟩,⟨4879007516068,6527127953240⟩,⟨46870898237212,93435105294998⟩,⟨-65567701118556,-2860248594918⟩,⟨-51136187947162,31646820768494⟩⟩⟩
noncomputable def wholeBoxes83 := wholeStep82.proposed :: wholeBoxes82
theorem wholeAccepted82 : StepValid wholeStep82.shape wholeBoxes82 wholeStep82.proposed := by
  dsimp only [StepValid,wholeStep82]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5004362062626,5072885063168⟩,⟨-25981153207033,-24164673675252⟩,⟨1364622176135,3150675017541⟩,⟨178513057799102,241749235872588⟩,⟨-42340977246782,25006144378385⟩,⟨-44482500957529,40144630007927⟩⟩⟩
noncomputable def wholeBoxes84 := wholeStep83.proposed :: wholeBoxes83
theorem wholeAccepted83 : StepValid wholeStep83.shape wholeBoxes83 wholeStep83.proposed := by
  dsimp only [StepValid,wholeStep83]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨461101382864,469396680513⟩,⟨1568162833662,1804035273767⟩,⟨125736140716,291533590096⟩,⟨-34983272425334,-26000961665095⟩,⟨-2834663687132,4817141242018⟩,⟨-4115988836799,3714603392643⟩⟩⟩
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
noncomputable def wholeStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨35372656148,37385964694⟩,⟨-766061446044,-725042737785⟩,⟨312815742780,315329962371⟩,⟨8883054590251,9572728519975⟩,⟨-6467888110707,-6405006849897⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes92 := wholeStep91.proposed :: wholeBoxes91
theorem wholeAccepted91 : StepValid wholeStep91.shape wholeBoxes91 wholeStep91.proposed := by
  dsimp only [StepValid,wholeStep91]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨496474039012,506782645207⟩,⟨802101387618,1078992535982⟩,⟨438551883496,606863552467⟩,⟨-26100217835083,-16428233145120⟩,⟨-9302551797839,-1587865607879⟩,⟨-4115988836799,3714603392643⟩⟩⟩
noncomputable def wholeBoxes93 := wholeStep92.proposed :: wholeBoxes92
theorem wholeAccepted92 : StepValid wholeStep92.shape wholeBoxes92 wholeStep92.proposed := by
  dsimp only [StepValid,wholeStep92]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep93 : Instruction 40 := ⟨.inv 17,⟨⟨507340798957,508333108400⟩,⟨2520383226112,2560338836291⟩,⟨0,0⟩,⟨2439291441574,4695713285828⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes94 := wholeStep93.proposed :: wholeBoxes93
theorem wholeAccepted93 : StepValid wholeStep93.shape wholeBoxes93 wholeStep93.proposed := by
  dsimp only [StepValid,wholeStep93]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨229084922115,234298929465⟩,⟨1508163767506,1678948063126⟩,⟨202358262828,280568961899⟩,⟨-7288103208078,-390931692240⟩,⟨-3295532460930,680472399449⟩,⟨-1902929761445,1717358726688⟩⟩⟩
noncomputable def wholeBoxes95 := wholeStep94.proposed :: wholeBoxes94
theorem wholeAccepted94 : StepValid wholeStep94.shape wholeBoxes94 wholeStep94.proposed := by
  dsimp only [StepValid,wholeStep94]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-765486389248,-717506532194⟩,⟨4819701481450,6165321746126⟩,⟨-6527127953240,-4879007516068⟩,⟨-93435105294998,-46870898237212⟩,⟨2860248594918,65567701118556⟩,⟨-31646820768494,51136187947162⟩⟩⟩
noncomputable def wholeBoxes96 := wholeStep95.proposed :: wholeBoxes95
theorem wholeAccepted95 : StepValid wholeStep95.shape wholeBoxes95 wholeStep95.proposed := by
  dsimp only [StepValid,wholeStep95]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3521369141184,3589892141726⟩,⟨-14996129979457,-13179650447676⟩,⟨-10041513293173,-8255460451767⟩,⟨38207054266892,101443232340378⟩,⟨26086972466692,93434094091859⟩,⟨-24993133778861,59633997186595⟩⟩⟩
noncomputable def wholeBoxes97 := wholeStep96.proposed :: wholeBoxes96
theorem wholeAccepted96 : StepValid wholeStep96.shape wholeBoxes96 wholeStep96.proposed := by
  dsimp only [StepValid,wholeStep96]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨443083132218,458281199967⟩,⟨259917832057,582509803221⟩,⟨-303351036000,-34557120721⟩,⟨-19549452277602,-8809658741000⟩,⟨-12234701304892,-1764734026684⟩,⟨-9941540785096,1915362852240⟩⟩⟩
noncomputable def wholeBoxes98 := wholeStep97.proposed :: wholeBoxes97
theorem wholeAccepted97 : StepValid wholeStep97.shape wholeBoxes97 wholeStep97.proposed := by
  dsimp only [StepValid,wholeStep97]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨325461884270,329490093836⟩,⟨1940466224332,1948197165466⟩,⟨872737354546,873596348008⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes99 := wholeStep98.proposed :: wholeBoxes98
theorem wholeAccepted98 : StepValid wholeStep98.shape wholeBoxes98 wholeStep98.proposed := by
  dsimp only [StepValid,wholeStep98]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-329490093836,-325461884270⟩,⟨-1948197165466,-1940466224332⟩,⟨-873596348008,-872737354546⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes100 := wholeStep99.proposed :: wholeBoxes99
theorem wholeAccepted99 : StepValid wholeStep99.shape wholeBoxes99 wholeStep99.proposed := by
  dsimp only [StepValid,wholeStep99]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨770021533940,774049743506⟩,⟨-1948197165466,-1940466224332⟩,⟨-873596348008,-872737354546⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes101 := wholeStep100.proposed :: wholeBoxes100
theorem wholeAccepted100 : StepValid wholeStep100.shape wholeBoxes100 wholeStep100.proposed := by
  dsimp only [StepValid,wholeStep100]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1336678641369,1354858783187⟩,⟨-8927505818921,-8626035508595⟩,⟨-4003206974364,-3879615793149⟩,⟨49301119090982,57742641575704⟩,⟨32001486490619,35920943091714⟩,⟨10019899007434,11566985866979⟩⟩⟩
noncomputable def wholeBoxes102 := wholeStep101.proposed :: wholeBoxes101
theorem wholeAccepted101 : StepValid wholeStep101.shape wholeBoxes101 wholeStep101.proposed := by
  dsimp only [StepValid,wholeStep101]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1354858783187,-1336678641369⟩,⟨8626035508595,8927505818921⟩,⟨3879615793149,4003206974364⟩,⟨-57742641575704,-49301119090982⟩,⟨-35920943091714,-32001486490619⟩,⟨-11566985866979,-10019899007434⟩⟩⟩
noncomputable def wholeBoxes103 := wholeStep102.proposed :: wholeBoxes102
theorem wholeAccepted102 : StepValid wholeStep102.shape wholeBoxes102 wholeStep102.proposed := by
  dsimp only [StepValid,wholeStep102]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-255347155411,-237167013593⟩,⟨8626035508595,8927505818921⟩,⟨3879615793149,4003206974364⟩,⟨-57742641575704,-49301119090982⟩,⟨-35920943091714,-32001486490619⟩,⟨-11566985866979,-10019899007434⟩⟩⟩
noncomputable def wholeBoxes104 := wholeStep103.proposed :: wholeBoxes103
theorem wholeAccepted103 : StepValid wholeStep103.shape wholeBoxes103 wholeStep103.proposed := by
  dsimp only [StepValid,wholeStep103]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-12026946090,-10643564559⟩,⟨414170477508,450512087683⟩,⟨72668477485,94426880432⟩,⟨-4819058706962,-4180346506389⟩,⟨1498045492465,1923259197293⟩,⟨2534635694898,2731000718243⟩⟩⟩
noncomputable def wholeBoxes105 := wholeStep104.proposed :: wholeBoxes104
theorem wholeAccepted104 : StepValid wholeStep104.shape wholeBoxes104 wholeStep104.proposed := by
  dsimp only [StepValid,wholeStep104]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨431056186128,447637635408⟩,⟨674088309565,1033021890904⟩,⟨-230682558515,59869759711⟩,⟨-24368510984564,-12990005247389⟩,⟨-10736655812427,158525170609⟩,⟨-7406905090198,4646363570483⟩⟩⟩
noncomputable def wholeBoxes106 := wholeStep105.proposed :: wholeBoxes105
theorem wholeAccepted105 : StepValid wholeStep105.shape wholeBoxes105 wholeStep105.proposed := by
  dsimp only [StepValid,wholeStep105]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-101738380002,-101308883270⟩,⟨-873596348008,-872737354546⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes107 := wholeStep106.proposed :: wholeBoxes106
theorem wholeAccepted106 : StepValid wholeStep106.shape wholeBoxes106 wholeStep106.proposed := by
  dsimp only [StepValid,wholeStep106]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4546532939,4791915577⟩,⟨27204437669,29591168749⟩,⟨40206963047,40417161119⟩,⟨-309006455280,-297780820045⟩,⟨244629257582,245740915920⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes108 := wholeStep107.proposed :: wholeBoxes107
theorem wholeAccepted107 : StepValid wholeStep107.shape wholeBoxes107 wholeStep107.proposed := by
  dsimp only [StepValid,wholeStep107]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨9834035497,10385064452⟩,⟨6637805402,15180758007⟩,⟨86966641867,87592282552⟩,⟨-904722608889,-769017865513⟩,⟨88809042402,99690417602⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes109 := wholeStep108.proposed :: wholeBoxes108
theorem wholeAccepted108 : StepValid wholeStep108.shape wholeBoxes108 wholeStep108.proposed := by
  dsimp only [StepValid,wholeStep108]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1452666040005,1470460484852⟩,⟨-7352777763090,-7050526267822⟩,⟨-1379571331906,-1310292078746⟩,⟨100422277411499,107614744011471⟩,⟨21157346226095,22899659968769⟩,⟨4679563043433,5107926701713⟩⟩⟩
noncomputable def wholeBoxes110 := wholeStep109.proposed :: wholeBoxes109
theorem wholeAccepted109 : StepValid wholeStep109.shape wholeBoxes109 wholeStep109.proposed := by
  dsimp only [StepValid,wholeStep109]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨12992649683,13888736166⟩,⟨-60678354643,-42757547644⟩,⟨101869363838,105424561714⟩,⟨-514814096435,-84710452517⟩,⟨-298239276307,-215962056461⟩,⟨-177952292444,-159031747801⟩⟩⟩
noncomputable def wholeBoxes111 := wholeStep110.proposed :: wholeBoxes110
theorem wholeAccepted110 : StepValid wholeStep110.shape wholeBoxes110 wholeStep110.proposed := by
  dsimp only [StepValid,wholeStep110]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-13888736166,-12992649683⟩,⟨42757547644,60678354643⟩,⟨-105424561714,-101869363838⟩,⟨84710452517,514814096435⟩,⟨215962056461,298239276307⟩,⟨159031747801,177952292444⟩⟩⟩
noncomputable def wholeBoxes112 := wholeStep111.proposed :: wholeBoxes111
theorem wholeAccepted111 : StepValid wholeStep111.shape wholeBoxes111 wholeStep111.proposed := by
  dsimp only [StepValid,wholeStep111]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-115627116168,-114301532953⟩,⟨-830838800364,-812058999903⟩,⟨-105424561714,-101869363838⟩,⟨2283733708069,2713837351987⟩,⟨215962056461,298239276307⟩,⟨159031747801,177952292444⟩⟩⟩
noncomputable def wholeBoxes113 := wholeStep112.proposed :: wholeBoxes112
theorem wholeAccepted112 : StepValid wholeStep112.shape wholeBoxes112 wholeStep112.proposed := by
  dsimp only [StepValid,wholeStep112]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨85655800539,90646142406⟩,⟨-595426787706,-554615878275⟩,⟨591962543194,613021926137⟩,⟨3173824010944,3848064737605⟩,⟨-3610563153222,-3162363358397⟩,⟨-2493685280253,-2279809538659⟩⟩⟩
noncomputable def wholeBoxes114 := wholeStep113.proposed :: wholeBoxes113
theorem wholeAccepted113 : StepValid wholeStep113.shape wholeBoxes113 wholeStep113.proposed := by
  dsimp only [StepValid,wholeStep113]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨113167764150,121227977172⟩,⟨-1402488581459,-1282014748820⟩,⟨668361339231,717764489117⟩,⟨19129333448235,21981914177410⟩,⟨-6618980670589,-5339011979329⟩,⟨-4508773506923,-4001845541832⟩⟩⟩
noncomputable def wholeBoxes115 := wholeStep114.proposed :: wholeBoxes114
theorem wholeAccepted114 : StepValid wholeStep114.shape wholeBoxes114 wholeStep114.proposed := by
  dsimp only [StepValid,wholeStep114]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-121227977172,-113167764150⟩,⟨1282014748820,1402488581459⟩,⟨-717764489117,-668361339231⟩,⟨-21981914177410,-19129333448235⟩,⟨5339011979329,6618980670589⟩,⟨4001845541832,4508773506923⟩⟩⟩
noncomputable def wholeBoxes116 := wholeStep115.proposed :: wholeBoxes115
theorem wholeAccepted115 : StepValid wholeStep115.shape wholeBoxes115 wholeStep115.proposed := by
  dsimp only [StepValid,wholeStep115]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨978283650604,986343863626⟩,⟨1282014748820,1402488581459⟩,⟨-717764489117,-668361339231⟩,⟨-21981914177410,-19129333448235⟩,⟨5339011979329,6618980670589⟩,⟨4001845541832,4508773506923⟩⟩⟩
noncomputable def wholeBoxes117 := wholeStep116.proposed :: wholeBoxes116
theorem wholeAccepted116 : StepValid wholeStep116.shape wholeBoxes116 wholeStep116.proposed := by
  dsimp only [StepValid,wholeStep116]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨123094446145,125915440230⟩,⟨765363216834,794730726077⟩,⟨180221560548,191812580703⟩,⟨-2771331386963,-2179593520283⟩,⟨-808667730597,-545730437431⟩,⟨-209350738644,-104049364932⟩⟩⟩
noncomputable def wholeBoxes118 := wholeStep117.proposed :: wholeBoxes117
theorem wholeAccepted117 : StepValid wholeStep117.shape wholeBoxes117 wholeStep117.proposed := by
  dsimp only [StepValid,wholeStep117]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11882403155,12159607644⟩,⟨168837847990,174745754498⟩,⟨21179993286,22173368134⟩,⟨628727562005,780817296803⟩,⟨87746932460,114425387930⟩,⟨-18551405634,-12847948435⟩⟩⟩
noncomputable def wholeBoxes119 := wholeStep118.proposed :: wholeBoxes118
theorem wholeAccepted118 : StepValid wholeStep118.shape wholeBoxes118 wholeStep118.proposed := by
  dsimp only [StepValid,wholeStep118]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨168813501356,179944132238⟩,⟨1465423712794,1884620989076⟩,⟨-4969047803,219563160662⟩,⟨-11058733057473,7161580437179⟩,⟨-5695710446023,6696024364218⟩,⟨-5787671087509,4714191877050⟩⟩⟩
noncomputable def wholeBoxes120 := wholeStep119.proposed :: wholeBoxes119
theorem wholeAccepted119 : StepValid wholeStep119.shape wholeBoxes119 wholeStep119.proposed := by
  dsimp only [StepValid,wholeStep119]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-179944132238,-168813501356⟩,⟨-1884620989076,-1465423712794⟩,⟨-219563160662,4969047803⟩,⟨-7161580437179,11058733057473⟩,⟨-6696024364218,5695710446023⟩,⟨-4714191877050,5787671087509⟩⟩⟩
noncomputable def wholeBoxes121 := wholeStep120.proposed :: wholeBoxes120
theorem wholeAccepted120 : StepValid wholeStep120.shape wholeBoxes120 wholeStep120.proposed := by
  dsimp only [StepValid,wholeStep120]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨49140789877,65485428109⟩,⟨-376457221570,213524350332⟩,⟨-17204897834,285538009702⟩,⟨-14449683645257,10667801365233⟩,⟨-9991556825148,6376182845472⟩,⟨-6617121638495,7505029814197⟩⟩⟩
noncomputable def wholeBoxes122 := wholeStep121.proposed :: wholeBoxes121
theorem wholeAccepted121 : StepValid wholeStep121.shape wholeBoxes121 wholeStep121.proposed := by
  dsimp only [StepValid,wholeStep121]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨27116077024857,28480205213127⟩,⟨-263690868028113,-219313307202415⟩,⟨-100419053233064,-65408602857327⟩,⟨2446322444501525,4292240564202644⟩,⟨464162448191068,2113077539242210⟩,⟨-539788711873994,1138837823894797⟩⟩⟩
noncomputable def wholeBoxes123 := wholeStep122.proposed :: wholeBoxes122
theorem wholeAccepted122 : StepValid wholeStep122.shape wholeBoxes122 wholeStep122.proposed := by
  dsimp only [StepValid,wholeStep122]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13780884429,14419763910⟩,⟨171370559248,182024212770⟩,⟨40352957838,43932533192⟩,⟨430786607592,660840796211⟩,⟨65685890194,155092430930⟩,⟨11130979085,43626945932⟩⟩⟩
noncomputable def wholeBoxes124 := wholeStep123.proposed :: wholeBoxes123
theorem wholeAccepted123 : StepValid wholeStep123.shape wholeBoxes123 wholeStep123.proposed := by
  dsimp only [StepValid,wholeStep123]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨339863184897,373509315325⟩,⟨768102129015,1966105258498⟩,⟨-321783888259,318158676421⟩,⟨-46022719851341,5044320331227⟩,⟨-19722933039868,13486072938709⟩,⟨-14829423961435,11264469993530⟩⟩⟩
noncomputable def wholeBoxes125 := wholeStep124.proposed :: wholeBoxes124
theorem wholeAccepted124 : StepValid wholeStep124.shape wholeBoxes124 wholeStep124.proposed := by
  dsimp only [StepValid,wholeStep124]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-373509315325,-339863184897⟩,⟨-1966105258498,-768102129015⟩,⟨-318158676421,321783888259⟩,⟨-5044320331227,46022719851341⟩,⟨-13486072938709,19722933039868⟩,⟨-11264469993530,14829423961435⟩⟩⟩
noncomputable def wholeBoxes126 := wholeStep125.proposed :: wholeBoxes125
theorem wholeAccepted125 : StepValid wholeStep125.shape wholeBoxes125 wholeStep125.proposed := by
  dsimp only [StepValid,wholeStep125]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨57546870803,107774450511⟩,⟨-1292016948933,264919761889⟩,⟨-548841234936,381653647970⟩,⟨-29412831315791,33032714603952⟩,⟨-24222728751136,19881458210477⟩,⟨-18671375083728,19475787531918⟩⟩⟩
noncomputable def wholeBoxes127 := wholeStep126.proposed :: wholeBoxes126
theorem wholeAccepted126 : StepValid wholeStep126.shape wholeBoxes126 wholeStep126.proposed := by
  dsimp only [StepValid,wholeStep126]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨239657075809,242100677325⟩,⟨1551642018509,1559928143615⟩,⟨305537942747,307566921911⟩,⟨-3925004181833,-3911333099600⟩,⟨-1548001508070,-1540144066720⟩,⟨-347049799190,-346367637584⟩⟩⟩
noncomputable def wholeBoxes128 := wholeStep127.proposed :: wholeBoxes127
theorem wholeAccepted127 : StepValid wholeStep127.shape wholeBoxes127 wholeStep127.proposed := by
  dsimp only [StepValid,wholeStep127]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1711109576154,-1623883799982⟩,⟨-5548553575541,-2662473440843⟩,⟨-515751551610,1461327392830⟩,⟨-19443280279980,101969793345626⟩,⟨-57627691487984,41437876094289⟩,⟨-46123019687959,49754609203898⟩⟩⟩
noncomputable def wholeBoxes129 := wholeStep128.proposed :: wholeBoxes128
theorem wholeAccepted128 : StepValid wholeStep128.shape wholeBoxes128 wholeStep128.proposed := by
  dsimp only [StepValid,wholeStep128]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-195955286075,-181799875429⟩,⟨-1872212962516,-1428449306781⟩,⟨-357570959149,-98821320163⟩,⟨-7028588344265,12283730592907⟩,⟨-7134239524229,6623771850969⟩,⟨-5308258116991,6533534844486⟩⟩⟩
noncomputable def wholeBoxes130 := wholeStep129.proposed :: wholeBoxes129
theorem wholeAccepted129 : StepValid wholeStep129.shape wholeBoxes129 wholeStep129.proposed := by
  dsimp only [StepValid,wholeStep129]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨43701789734,60300801896⟩,⟨-320570944007,131478836834⟩,⟨-52033016402,208745601748⟩,⟨-10953592526098,8372397493307⟩,⟨-8682241032299,5083627784249⟩,⟨-5655307916181,6187167206902⟩⟩⟩
noncomputable def wholeBoxes131 := wholeStep130.proposed :: wholeBoxes130
theorem wholeAccepted130 : StepValid wholeStep130.shape wholeBoxes130 wholeStep130.proposed := by
  dsimp only [StepValid,wholeStep130]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨2571958872,6418900768⟩,⟨-113851231819,36707982464⟩,⟨-34374672072,50719295016⟩,⟨-3669968213961,3897781525098⟩,⟨-2888251882572,2065822002626⟩,⟨-2045717071295,2093824145647⟩⟩⟩
noncomputable def wholeBoxes132 := wholeStep131.proposed :: wholeBoxes131
theorem wholeAccepted131 : StepValid wholeStep131.shape wholeBoxes131 wholeStep131.proposed := by
  dsimp only [StepValid,wholeStep131]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨1736995205,3307092547⟩,⟨-35162311158,14421456024⟩,⟨-5707320478,22896578554⟩,⟨-1278128743811,1105268916546⟩,⟨-1074047524730,607528747140⟩,⟨-640068293496,757910802878⟩⟩⟩
noncomputable def wholeBoxes133 := wholeStep132.proposed :: wholeBoxes132
theorem wholeAccepted132 : StepValid wholeStep132.shape wholeBoxes132 wholeStep132.proposed := by
  dsimp only [StepValid,wholeStep132]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨3015246052,5788572921⟩,⟨-85119558872,13382683714⟩,⟨-20560323414,34742970756⟩,⟨-2391330319176,2563927814613⟩,⟨-2052570730591,1300276617532⟩,⟨-1256202144660,1388654325272⟩⟩⟩
noncomputable def wholeBoxes134 := wholeStep133.proposed :: wholeBoxes133
theorem wholeAccepted133 : StepValid wholeStep133.shape wholeBoxes133 wholeStep133.proposed := by
  dsimp only [StepValid,wholeStep133]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-5788572921,-3015246052⟩,⟨-13382683714,85119558872⟩,⟨-34742970756,20560323414⟩,⟨-2563927814613,2391330319176⟩,⟨-1300276617532,2052570730591⟩,⟨-1388654325272,1256202144660⟩⟩⟩
noncomputable def wholeBoxes135 := wholeStep134.proposed :: wholeBoxes134
theorem wholeAccepted134 : StepValid wholeStep134.shape wholeBoxes134 wholeStep134.proposed := by
  dsimp only [StepValid,wholeStep134]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨-3216614049,3403654716⟩,⟨-127233915533,121827541336⟩,⟨-69117642828,71279618430⟩,⟨-6233896028574,6289111844274⟩,⟨-4188528500104,4118392733217⟩,⟨-3434371396567,3350026290307⟩⟩⟩
noncomputable def wholeBoxes136 := wholeStep135.proposed :: wholeBoxes135
theorem wholeAccepted135 : StepValid wholeStep135.shape wholeBoxes135 wholeStep135.proposed := by
  dsimp only [StepValid,wholeStep135]
  exact ⟨by decide,by decide⟩
noncomputable def wholeProgram : List (Instruction 40) := [wholeStep0,wholeStep1,wholeStep2,wholeStep3,wholeStep4,wholeStep5,wholeStep6,wholeStep7,wholeStep8,wholeStep9,wholeStep10,wholeStep11,wholeStep12,wholeStep13,wholeStep14,wholeStep15,wholeStep16,wholeStep17,wholeStep18,wholeStep19,wholeStep20,wholeStep21,wholeStep22,wholeStep23,wholeStep24,wholeStep25,wholeStep26,wholeStep27,wholeStep28,wholeStep29,wholeStep30,wholeStep31,wholeStep32,wholeStep33,wholeStep34,wholeStep35,wholeStep36,wholeStep37,wholeStep38,wholeStep39,wholeStep40,wholeStep41,wholeStep42,wholeStep43,wholeStep44,wholeStep45,wholeStep46,wholeStep47,wholeStep48,wholeStep49,wholeStep50,wholeStep51,wholeStep52,wholeStep53,wholeStep54,wholeStep55,wholeStep56,wholeStep57,wholeStep58,wholeStep59,wholeStep60,wholeStep61,wholeStep62,wholeStep63,wholeStep64,wholeStep65,wholeStep66,wholeStep67,wholeStep68,wholeStep69,wholeStep70,wholeStep71,wholeStep72,wholeStep73,wholeStep74,wholeStep75,wholeStep76,wholeStep77,wholeStep78,wholeStep79,wholeStep80,wholeStep81,wholeStep82,wholeStep83,wholeStep84,wholeStep85,wholeStep86,wholeStep87,wholeStep88,wholeStep89,wholeStep90,wholeStep91,wholeStep92,wholeStep93,wholeStep94,wholeStep95,wholeStep96,wholeStep97,wholeStep98,wholeStep99,wholeStep100,wholeStep101,wholeStep102,wholeStep103,wholeStep104,wholeStep105,wholeStep106,wholeStep107,wholeStep108,wholeStep109,wholeStep110,wholeStep111,wholeStep112,wholeStep113,wholeStep114,wholeStep115,wholeStep116,wholeStep117,wholeStep118,wholeStep119,wholeStep120,wholeStep121,wholeStep122,wholeStep123,wholeStep124,wholeStep125,wholeStep126,wholeStep127,wholeStep128,wholeStep129,wholeStep130,wholeStep131,wholeStep132,wholeStep133,wholeStep134,wholeStep135]
theorem wholeAccepted : Accepted wholeProgram wholeInitial :=
  ⟨wholeAccepted0,⟨wholeAccepted1,⟨wholeAccepted2,⟨wholeAccepted3,⟨wholeAccepted4,⟨wholeAccepted5,⟨wholeAccepted6,⟨wholeAccepted7,⟨wholeAccepted8,⟨wholeAccepted9,⟨wholeAccepted10,⟨wholeAccepted11,⟨wholeAccepted12,⟨wholeAccepted13,⟨wholeAccepted14,⟨wholeAccepted15,⟨wholeAccepted16,⟨wholeAccepted17,⟨wholeAccepted18,⟨wholeAccepted19,⟨wholeAccepted20,⟨wholeAccepted21,⟨wholeAccepted22,⟨wholeAccepted23,⟨wholeAccepted24,⟨wholeAccepted25,⟨wholeAccepted26,⟨wholeAccepted27,⟨wholeAccepted28,⟨wholeAccepted29,⟨wholeAccepted30,⟨wholeAccepted31,⟨wholeAccepted32,⟨wholeAccepted33,⟨wholeAccepted34,⟨wholeAccepted35,⟨wholeAccepted36,⟨wholeAccepted37,⟨wholeAccepted38,⟨wholeAccepted39,⟨wholeAccepted40,⟨wholeAccepted41,⟨wholeAccepted42,⟨wholeAccepted43,⟨wholeAccepted44,⟨wholeAccepted45,⟨wholeAccepted46,⟨wholeAccepted47,⟨wholeAccepted48,⟨wholeAccepted49,⟨wholeAccepted50,⟨wholeAccepted51,⟨wholeAccepted52,⟨wholeAccepted53,⟨wholeAccepted54,⟨wholeAccepted55,⟨wholeAccepted56,⟨wholeAccepted57,⟨wholeAccepted58,⟨wholeAccepted59,⟨wholeAccepted60,⟨wholeAccepted61,⟨wholeAccepted62,⟨wholeAccepted63,⟨wholeAccepted64,⟨wholeAccepted65,⟨wholeAccepted66,⟨wholeAccepted67,⟨wholeAccepted68,⟨wholeAccepted69,⟨wholeAccepted70,⟨wholeAccepted71,⟨wholeAccepted72,⟨wholeAccepted73,⟨wholeAccepted74,⟨wholeAccepted75,⟨wholeAccepted76,⟨wholeAccepted77,⟨wholeAccepted78,⟨wholeAccepted79,⟨wholeAccepted80,⟨wholeAccepted81,⟨wholeAccepted82,⟨wholeAccepted83,⟨wholeAccepted84,⟨wholeAccepted85,⟨wholeAccepted86,⟨wholeAccepted87,⟨wholeAccepted88,⟨wholeAccepted89,⟨wholeAccepted90,⟨wholeAccepted91,⟨wholeAccepted92,⟨wholeAccepted93,⟨wholeAccepted94,⟨wholeAccepted95,⟨wholeAccepted96,⟨wholeAccepted97,⟨wholeAccepted98,⟨wholeAccepted99,⟨wholeAccepted100,⟨wholeAccepted101,⟨wholeAccepted102,⟨wholeAccepted103,⟨wholeAccepted104,⟨wholeAccepted105,⟨wholeAccepted106,⟨wholeAccepted107,⟨wholeAccepted108,⟨wholeAccepted109,⟨wholeAccepted110,⟨wholeAccepted111,⟨wholeAccepted112,⟨wholeAccepted113,⟨wholeAccepted114,⟨wholeAccepted115,⟨wholeAccepted116,⟨wholeAccepted117,⟨wholeAccepted118,⟨wholeAccepted119,⟨wholeAccepted120,⟨wholeAccepted121,⟨wholeAccepted122,⟨wholeAccepted123,⟨wholeAccepted124,⟨wholeAccepted125,⟨wholeAccepted126,⟨wholeAccepted127,⟨wholeAccepted128,⟨wholeAccepted129,⟨wholeAccepted130,⟨wholeAccepted131,⟨wholeAccepted132,⟨wholeAccepted133,⟨wholeAccepted134,⟨wholeAccepted135,True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
noncomputable def whole_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨49140789877,65485428109⟩,⟨-376457221570,213524350332⟩,⟨-17204897834,285538009702⟩,⟨-14449683645257,10667801365233⟩,⟨-9991556825148,6376182845472⟩,⟨-6617121638495,7505029814197⟩⟩
theorem whole_m11_eq : (finalBoxes wholeProgram wholeInitial).getD 14 (zeroBox 40)=whole_m11 := rfl
noncomputable def whole_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨-3216614049,3403654716⟩,⟨-127233915533,121827541336⟩,⟨-69117642828,71279618430⟩,⟨-6233896028574,6289111844274⟩,⟨-4188528500104,4118392733217⟩,⟨-3434371396567,3350026290307⟩⟩
theorem whole_kdet_eq : (finalBoxes wholeProgram wholeInitial).getD 0 (zeroBox 40)=whole_kdet := rfl
theorem sameShape : shapes centerProgram=shapes wholeProgram := by decide
theorem kernelShape : shapes wholeProgram =
    shapes CorrectionFactorizedProgramKernel.kernelProgram := by decide
attribute [local irreducible] wholeProgram centerProgram
noncomputable def inputJets (u rho : ℝ) : List BivariateJet2 :=
  [BivariateJet2.affineA (527/5120) u, BivariateJet2.affineZ (593/5120) rho,
    BivariateJet2.const 1, BivariateJet2.const 2]
noncomputable def outputJet_m11 (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 14 zeroJet
theorem output_value_m11 (u rho t : ℝ) : (outputJet_m11 u rho).value t =
    Correction.Natural.m11 (527/5120+t*(u-(527/5120))) ((527/5120+t*(u-(527/5120)))+(593/5120+t*(rho-(593/5120)))*(1/2-(527/5120+t*(u-(527/5120))))) := by
  exact CorrectionFactorizedProgramKernel.output_value_m11_of_shapes wholeProgram kernelShape (527/5120) (593/5120) u rho t
theorem output_value_one_m11 (u rho : ℝ) : (outputJet_m11 u rho).value 1 =
    Correction.Natural.m11 u (u+rho*(1/2-u)) := by simp [output_value_m11]
noncomputable def outputJet_kdet (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 0 zeroJet
theorem output_value_kdet (u rho t : ℝ) : (outputJet_kdet u rho).value t =
    Correction.Natural.kdet (527/5120+t*(u-(527/5120))) ((527/5120+t*(u-(527/5120)))+(593/5120+t*(rho-(593/5120)))*(1/2-(527/5120+t*(u-(527/5120))))) := by
  exact CorrectionFactorizedProgramKernel.output_value_kdet_of_shapes wholeProgram kernelShape (527/5120) (593/5120) u rho t
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
    (⟨⟨127345780326,127345780327⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩ : DyadicBivariateJetEnclosure 40).Contains (BivariateJet2.affineZ (593/5120) x) 0 := by
  apply DyadicBivariateJetEnclosure.contains_coordinateZ
  norm_num [DyadicInterval.Contains,DyadicInterval.scale]
private theorem whole_Z {x t : ℝ} (hx : x∈Icc (73/640:ℝ) (301/2560)) (ht : t∈Icc (0:ℝ) 1) :
    (⟨⟨125413045043,129278515610⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩ : DyadicBivariateJetEnclosure 40).Contains (BivariateJet2.affineZ (593/5120) x) t := by
  apply DyadicBivariateJetEnclosure.contains_coordinateZ
  change (⟨125413045043,129278515610⟩ : DyadicInterval 40).Contains ((Jet2.segment (593/5120) x).value t)
  apply DyadicInterval.contains_segment _ _ ht
  · norm_num [DyadicInterval.Contains,DyadicInterval.scale]
  · norm_num [DyadicInterval.Contains,DyadicInterval.scale]
    constructor <;> linarith [hx.1,hx.2]
theorem initial_center (a z : ℝ) : RegistersContain centerInitial (inputJets a z) 0 := by
  simpa [centerInitial,inputJets,DyadicBivariateJetEnclosure.const,DyadicInterval.ofInt,DyadicInterval.scale] using
    ((((RegistersContain.nil 40 0).cons (DyadicBivariateJetEnclosure.contains_const 40 2 0)).cons
      (DyadicBivariateJetEnclosure.contains_const 40 1 0)).cons (center_Z z)).cons (center_A a)

theorem initial_whole {a z : ℝ} (ha : a ∈ Icc (263/2560:ℝ) (33/320))
    (hz : z ∈ Icc (73/640:ℝ) (301/2560)) :
    ∀ t ∈ Icc (0:ℝ) 1, RegistersContain wholeInitial (inputJets a z) t := by
  intro t ht
  simpa [wholeInitial,inputJets,DyadicBivariateJetEnclosure.const,DyadicInterval.ofInt,DyadicInterval.scale] using
    ((((RegistersContain.nil 40 t).cons (DyadicBivariateJetEnclosure.contains_const 40 2 t)).cons
      (DyadicBivariateJetEnclosure.contains_const 40 1 t)).cons (whole_Z hz ht)).cons (whole_A ha ht)

theorem initial_sound (a z : ℝ) : ∀ i, ((inputJets a z).getD i zeroJet).DirectionalSoundOn
    (a-527/5120) (z-593/5120) (Icc (0:ℝ) 1) := by
  intro i t ht
  have hconst (c : ℝ) : (BivariateJet2.const c).DirectionalSoundAt (a-527/5120) (z-593/5120) t := by
    simpa only [BivariateJet2.DirectionalSoundAt,BivariateJet2.projection_const] using Jet2.soundAt_const c t
  have h : RegistersSound (inputJets a z) (a-527/5120) (z-593/5120) t :=
    ((((RegistersSound.nil _ _ t).cons (hconst 2)).cons (hconst 1)).cons
      (BivariateJet2.soundOn_affineZ (593/5120) z (a-527/5120) _ t ht)).cons
      (BivariateJet2.soundOn_affineA (527/5120) a (z-593/5120) _ t ht)
  exact h i

theorem taylor_positive_m11 : 0 < BivariateJetEnclosure.taylorLower
    center_m11.toReal whole_m11.toReal (1/5120) (9/5120) := by
  norm_num [BivariateJetEnclosure.taylorLower,JetBounds.Interval.magnitude,
    DyadicBivariateJetEnclosure.toReal,DyadicInterval.toReal,DyadicInterval.scale,center_m11,whole_m11]
theorem positive_m11 {a z : ℝ} (ha : a∈Icc (263/2560:ℝ) (33/320))
    (hz : z∈Icc (73/640:ℝ) (301/2560)) : 0 < Correction.Natural.m11 a (a+z*(1/2-a)) := by
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
    (hz : z∈Icc (73/640:ℝ) (301/2560)) : 0 < Correction.Natural.kdet a (a+z*(1/2-a)) := by
  have hp := value_pos_of_accepted_taylor centerProgram wholeProgram 0 sameShape
    (initial_center a z) (initial_whole ha hz) (initial_sound a z) centerAccepted wholeAccepted
    (show (0:ℝ)≤1/5120 by norm_num) (show (0:ℝ)≤9/5120 by norm_num)
    (by rw [abs_le]; constructor <;> linarith [ha.1,ha.2])
    (by rw [abs_le]; constructor <;> linarith [hz.1,hz.2])
    (by rw [center_kdet_eq,whole_kdet_eq]; exact taylor_positive_kdet)
  change 0 < (outputJet_kdet a z).value 1 at hp
  simpa only [output_value_one_kdet] using hp

theorem _root_.solution {u rho : ℝ} (hu : u∈Icc (263/2560:ℝ) (33/320))
    (hr : rho∈Icc (73/640:ℝ) (301/2560)) (hr1 : rho < 1) :
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




end GeneralCK.Certificates.LaneCB.RB2Cell000058
end

