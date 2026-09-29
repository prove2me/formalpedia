-- Prove2me | solution 1 for GeneralCK.Certificates.LaneCB.RB2Cell000057.actual_minors_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-25T14:19:58.674771+00:00
-- url     : https://prove2.me/submissions/1f84ff5d-f897-495b-9d6c-f651d06572f2

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

namespace LaneCBRB2Cell000057Endpoints
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
noncomputable def out_w0 : DyadicInterval 40 := ⟨-2504150381952,-2504150324096⟩
theorem checked_w0 : DyadicFastLog.check 112742891520 1099511627776 3 16 (lift40 out_w0)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w0 : out_w0.Contains (Real.log ((112742891520:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w0

noncomputable def out_w1 : DyadicInterval 40 := ⟨-118951416704,-118951416640⟩
theorem checked_w1 : DyadicFastLog.check 986768736256 1099511627776 0 16 (lift40 out_w1)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w1 : out_w1.Contains (Real.log ((986768736256:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w1

noncomputable def out_w2 : DyadicInterval 40 := ⟨-2086122246080,-2086122207360⟩
theorem checked_w2 : DyadicFastLog.check 164894238310 1099511627776 2 16 (lift40 out_w2)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w2 : out_w2.Contains (Real.log ((164894238310:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w2

noncomputable def out_w3 : DyadicInterval 40 := ⟨-2086122246080,-2086122207360⟩
theorem checked_w3 : DyadicFastLog.check 164894238311 1099511627776 2 16 (lift40 out_w3)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w3 : out_w3.Contains (Real.log ((164894238311:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w3

noncomputable def out_w4 : DyadicInterval 40 := ⟨-178653211200,-178653211136⟩
theorem checked_w4 : DyadicFastLog.check 934617389465 1099511627776 0 16 (lift40 out_w4)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w4 : out_w4.Contains (Real.log ((934617389465:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w4

noncomputable def out_w5 : DyadicInterval 40 := ⟨-178653211200,-178653211136⟩
theorem checked_w5 : DyadicFastLog.check 934617389466 1099511627776 0 16 (lift40 out_w5)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w5 : out_w5.Contains (Real.log ((934617389466:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w5

noncomputable def out_w6 : DyadicInterval 40 := ⟨762123383616,762123402880⟩
theorem checked_w6 : DyadicFastLog.check 1099511627776 2199023255552 1 16 (lift40 out_w6.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w6 : out_w6.Contains (Real.log ((2199023255552:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w6

noncomputable def out_w7 : DyadicInterval 40 := ⟨91535225664,91535225728⟩
theorem checked_w7 : DyadicFastLog.check 1099511627776 1194965015552 0 16 (lift40 out_w7.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w7 : out_w7.Contains (Real.log ((1194965015552:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w7

noncomputable def out_w8 : DyadicInterval 40 := ⟨-99853334784,-99853334720⟩
theorem checked_w8 : DyadicFastLog.check 1004058240000 1099511627776 0 16 (lift40 out_w8)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w8 : out_w8.Contains (Real.log ((1004058240000:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w8

noncomputable def out_w9 : DyadicInterval 40 := ⟨91535348416,91535348480⟩
theorem checked_w9 : DyadicFastLog.check 1099511627776 1194965148928 0 16 (lift40 out_w9.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w9 : out_w9.Contains (Real.log ((1194965148928:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w9

noncomputable def out_w10 : DyadicInterval 40 := ⟨-99853480832,-99853480768⟩
theorem checked_w10 : DyadicFastLog.check 1004058106624 1099511627776 0 16 (lift40 out_w10)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w10 : out_w10.Contains (Real.log ((1004058106624:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w10

noncomputable def out_w11 : DyadicInterval 40 := ⟨-8318132416,-8318132352⟩
theorem checked_w11 : DyadicFastLog.check 1091224880760 1099511627776 0 16 (lift40 out_w11)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w11 : out_w11.Contains (Real.log ((1091224880760:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w11

noncomputable def out_w12 : DyadicInterval 40 := ⟨-8318109120,-8318109056⟩
theorem checked_w12 : DyadicFastLog.check 1091224903919 1099511627776 0 16 (lift40 out_w12)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w12 : out_w12.Contains (Real.log ((1091224903919:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w12

noncomputable def out_w13 : DyadicInterval 40 := ⟨191388560448,191388560512⟩
theorem checked_w13 : DyadicFastLog.check 1099511627776 1308567448622 0 16 (lift40 out_w13.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w13 : out_w13.Contains (Real.log ((1308567448622:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w13

noncomputable def out_w14 : DyadicInterval 40 := ⟨191388829184,191388829248⟩
theorem checked_w14 : DyadicFastLog.check 1099511627776 1308567768506 0 16 (lift40 out_w14.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w14 : out_w14.Contains (Real.log ((1308567768506:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w14

noncomputable def out_w15 : DyadicInterval 40 := ⟨2385198907456,2385198965312⟩
theorem checked_w15 : DyadicFastLog.check 1099511627776 9623344627868 3 16 (lift40 out_w15.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w15 : out_w15.Contains (Real.log ((9623344627868:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w15

noncomputable def out_w16 : DyadicInterval 40 := ⟨2385198907456,2385198965312⟩
theorem checked_w16 : DyadicFastLog.check 1099511627776 9623344627869 3 16 (lift40 out_w16.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w16 : out_w16.Contains (Real.log ((9623344627869:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w16

noncomputable def out_w17 : DyadicInterval 40 := ⟨1907468996160,1907469034752⟩
theorem checked_w17 : DyadicFastLog.check 1099511627776 6232010880211 2 16 (lift40 out_w17.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w17 : out_w17.Contains (Real.log ((6232010880211:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w17

noncomputable def out_w18 : DyadicInterval 40 := ⟨1907468996160,1907469034752⟩
theorem checked_w18 : DyadicFastLog.check 1099511627776 6232010880257 2 16 (lift40 out_w18.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w18 : out_w18.Contains (Real.log ((6232010880257:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w18

noncomputable def out_w19 : DyadicInterval 40 := ⟨-2506246686976,-2506246629120⟩
theorem checked_w19 : DyadicFastLog.check 112528143155 1099511627776 3 16 (lift40 out_w19)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w19 : out_w19.Contains (Real.log ((112528143155:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w19

noncomputable def out_w20 : DyadicInterval 40 := ⟨-2502058066176,-2502058008320⟩
theorem checked_w20 : DyadicFastLog.check 112957639885 1099511627776 3 16 (lift40 out_w20)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w20 : out_w20.Contains (Real.log ((112957639885:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w20

noncomputable def out_w21 : DyadicInterval 40 := ⟨-119190727104,-119190727040⟩
theorem checked_w21 : DyadicFastLog.check 986553987891 1099511627776 0 16 (lift40 out_w21)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w21 : out_w21.Contains (Real.log ((986553987891:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w21

noncomputable def out_w22 : DyadicInterval 40 := ⟨-118712158400,-118712158336⟩
theorem checked_w22 : DyadicFastLog.check 986983484621 1099511627776 0 16 (lift40 out_w22)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w22 : out_w22.Contains (Real.log ((986983484621:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w22

noncomputable def out_w23 : DyadicInterval 40 := ⟨-2092865438912,-2092865400128⟩
theorem checked_w23 : DyadicFastLog.check 163886053457 1099511627776 2 16 (lift40 out_w23)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w23 : out_w23.Contains (Real.log ((163886053457:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w23

noncomputable def out_w24 : DyadicInterval 40 := ⟨-2079415153088,-2079415114368⟩
theorem checked_w24 : DyadicFastLog.check 165903178138 1099511627776 2 16 (lift40 out_w24)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w24 : out_w24.Contains (Real.log ((165903178138:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w24

noncomputable def out_w25 : DyadicInterval 40 := ⟨-179840799104,-179840799040⟩
theorem checked_w25 : DyadicFastLog.check 933608449638 1099511627776 0 16 (lift40 out_w25)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w25 : out_w25.Contains (Real.log ((933608449638:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w25

noncomputable def out_w26 : DyadicInterval 40 := ⟨-177467791936,-177467791872⟩
theorem checked_w26 : DyadicFastLog.check 935625574319 1099511627776 0 16 (lift40 out_w26)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w26 : out_w26.Contains (Real.log ((935625574319:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w26

noncomputable def out_w27 : DyadicInterval 40 := ⟨88979814784,88979814848⟩
theorem checked_w27 : DyadicFastLog.check 1099511627776 1192190983168 0 16 (lift40 out_w27.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w27 : out_w27.Contains (Real.log ((1192190983168:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w27

noncomputable def out_w28 : DyadicInterval 40 := ⟨-96819770496,-96819770432⟩
theorem checked_w28 : DyadicFastLog.check 1006832272384 1099511627776 0 16 (lift40 out_w28)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w28 : out_w28.Contains (Real.log ((1006832272384:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w28

noncomputable def out_w29 : DyadicInterval 40 := ⟨94112211456,94112211520⟩
theorem checked_w29 : DyadicFastLog.check 1099511627776 1197769005312 0 16 (lift40 out_w29.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w29 : out_w29.Contains (Real.log ((1197769005312:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w29

noncomputable def out_w30 : DyadicInterval 40 := ⟨-102928188608,-102928188544⟩
theorem checked_w30 : DyadicFastLog.check 1001254250240 1099511627776 0 16 (lift40 out_w30)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w30 : out_w30.Contains (Real.log ((1001254250240:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w30

noncomputable def out_w31 : DyadicInterval 40 := ⟨-8815977088,-8815977024⟩
theorem checked_w31 : DyadicFastLog.check 1090730900045 1099511627776 0 16 (lift40 out_w31)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w31 : out_w31.Contains (Real.log ((1090730900045:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w31

noncomputable def out_w32 : DyadicInterval 40 := ⟨-7839955712,-7839955648⟩
theorem checked_w32 : DyadicFastLog.check 1091699556763 1099511627776 0 16 (lift40 out_w32)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w32 : out_w32.Contains (Real.log ((1091699556763:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w32

noncomputable def out_w33 : DyadicInterval 40 := ⟨185799585280,185799585344⟩
theorem checked_w33 : DyadicFastLog.check 1099511627776 1301932689760 0 16 (lift40 out_w33.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w33 : out_w33.Contains (Real.log ((1301932689760:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w33

noncomputable def out_w34 : DyadicInterval 40 := ⟨197040400000,197040400064⟩
theorem checked_w34 : DyadicFastLog.check 1099511627776 1315311219318 0 16 (lift40 out_w34.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w34 : out_w34.Contains (Real.log ((1315311219318:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w34

noncomputable def out_w35 : DyadicInterval 40 := ⟨2382867281216,2382867339072⟩
theorem checked_w35 : DyadicFastLog.check 1099511627776 9602958969568 3 16 (lift40 out_w35.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w35 : out_w35.Contains (Real.log ((9602958969568:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w35

noncomputable def out_w36 : DyadicInterval 40 := ⟨2387534470720,2387534528576⟩
theorem checked_w36 : DyadicFastLog.check 1099511627776 9643808094024 3 16 (lift40 out_w36.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w36 : out_w36.Contains (Real.log ((9643808094024:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w36

noncomputable def out_w37 : DyadicInterval 40 := ⟨1899574315328,1899574353920⟩
theorem checked_w37 : DyadicFastLog.check 1099511627776 6187424241584 2 16 (lift40 out_w37.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w37 : out_w37.Contains (Real.log ((6187424241584:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w37

noncomputable def out_w38 : DyadicInterval 40 := ⟨1915397608256,1915397646848⟩
theorem checked_w38 : DyadicFastLog.check 1099511627776 6277112521221 2 16 (lift40 out_w38.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w38 : out_w38.Contains (Real.log ((6277112521221:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w38

end LaneCBRB2Cell000057Endpoints

namespace GeneralCK.Certificates.LaneCB.RB2Cell000057
open Set LaneCBRB2Cell000057Endpoints
open BivariateJetProgram (RegistersContain RegistersSound zeroBox zeroJet)
open BivariateProvedProgram
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
theorem lc0 : ProvedTranscendental.LogEncloses (⟨112742891520,112742891520⟩ : DyadicInterval 40) (⟨-2504150381952,-2504150324096⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc1 : ProvedTranscendental.LogEncloses (⟨986768736256,986768736256⟩ : DyadicInterval 40) (⟨-118951416704,-118951416640⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w1
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w1
theorem lc2 : ProvedTranscendental.LogEncloses (⟨164894238310,164894238311⟩ : DyadicInterval 40) (⟨-2086122246080,-2086122207360⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w2
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w3
theorem lc3 : ProvedTranscendental.LogEncloses (⟨934617389465,934617389466⟩ : DyadicInterval 40) (⟨-178653211200,-178653211136⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w4
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w5
theorem lc4 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w6
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w6
theorem lc5 : ProvedTranscendental.LogEncloses (⟨1194965015552,1194965015552⟩ : DyadicInterval 40) (⟨91535225664,91535225728⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w7
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w7
theorem lc6 : ProvedTranscendental.LogEncloses (⟨1004058240000,1004058240000⟩ : DyadicInterval 40) (⟨-99853334784,-99853334720⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
theorem lc7 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w6
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w6
theorem lc8 : ProvedTranscendental.LogEncloses (⟨1194965148928,1194965148928⟩ : DyadicInterval 40) (⟨91535348416,91535348480⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w9
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w9
theorem lc9 : ProvedTranscendental.LogEncloses (⟨1004058106624,1004058106624⟩ : DyadicInterval 40) (⟨-99853480832,-99853480768⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w10
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w10
theorem lc10 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w6
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w6
theorem lc11 : ProvedTranscendental.LogEncloses (⟨1091224880760,1091224903919⟩ : DyadicInterval 40) (⟨-8318132416,-8318109056⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w11
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w12
theorem lc12 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w6
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w6
theorem lc13 : ProvedTranscendental.LogEncloses (⟨1194965015552,1194965148928⟩ : DyadicInterval 40) (⟨91535225664,91535348480⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w7
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w9
theorem lc14 : ProvedTranscendental.LogEncloses (⟨1004058106624,1004058240000⟩ : DyadicInterval 40) (⟨-99853480832,-99853334720⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w10
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
theorem lc15 : ProvedTranscendental.LogEncloses (⟨1091224880760,1091224903919⟩ : DyadicInterval 40) (⟨-8318132416,-8318109056⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w11
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w12
theorem lc16 : ProvedTranscendental.LogEncloses (⟨1308567448622,1308567768506⟩ : DyadicInterval 40) (⟨191388560448,191388829248⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w13
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w14
theorem lc17 : ProvedTranscendental.LogEncloses (⟨9623344627868,9623344627869⟩ : DyadicInterval 40) (⟨2385198907456,2385198965312⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w15
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w16
theorem lc18 : ProvedTranscendental.LogEncloses (⟨6232010880211,6232010880257⟩ : DyadicInterval 40) (⟨1907468996160,1907469034752⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w17
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w18
theorem lc19 : ProvedTranscendental.LogEncloses (⟨112528143155,112957639885⟩ : DyadicInterval 40) (⟨-2506246686976,-2502058008320⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w19
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w20
theorem lc20 : ProvedTranscendental.LogEncloses (⟨986553987891,986983484621⟩ : DyadicInterval 40) (⟨-119190727104,-118712158336⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w21
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w22
theorem lc21 : ProvedTranscendental.LogEncloses (⟨163886053457,165903178138⟩ : DyadicInterval 40) (⟨-2092865438912,-2079415114368⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w23
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w24
theorem lc22 : ProvedTranscendental.LogEncloses (⟨933608449638,935625574319⟩ : DyadicInterval 40) (⟨-179840799104,-177467791872⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w25
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w26
theorem lc23 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w6
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w6
theorem lc24 : ProvedTranscendental.LogEncloses (⟨1192190983168,1192190983168⟩ : DyadicInterval 40) (⟨88979814784,88979814848⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w27
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w27
theorem lc25 : ProvedTranscendental.LogEncloses (⟨1006832272384,1006832272384⟩ : DyadicInterval 40) (⟨-96819770496,-96819770432⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w28
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w28
theorem lc26 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w6
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w6
theorem lc27 : ProvedTranscendental.LogEncloses (⟨1197769005312,1197769005312⟩ : DyadicInterval 40) (⟨94112211456,94112211520⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w29
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w29
theorem lc28 : ProvedTranscendental.LogEncloses (⟨1001254250240,1001254250240⟩ : DyadicInterval 40) (⟨-102928188608,-102928188544⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w30
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w30
theorem lc29 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w6
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w6
theorem lc30 : ProvedTranscendental.LogEncloses (⟨1090730900045,1091699556763⟩ : DyadicInterval 40) (⟨-8815977088,-7839955648⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w31
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w32
theorem lc31 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w6
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w6
theorem lc32 : ProvedTranscendental.LogEncloses (⟨1192190983168,1197769005312⟩ : DyadicInterval 40) (⟨88979814784,94112211520⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w27
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w29
theorem lc33 : ProvedTranscendental.LogEncloses (⟨1001254250240,1006832272384⟩ : DyadicInterval 40) (⟨-102928188608,-96819770432⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w30
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w28
theorem lc34 : ProvedTranscendental.LogEncloses (⟨1090730900045,1091699556763⟩ : DyadicInterval 40) (⟨-8815977088,-7839955648⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w31
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w32
theorem lc35 : ProvedTranscendental.LogEncloses (⟨1301932689760,1315311219318⟩ : DyadicInterval 40) (⟨185799585280,197040400064⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w33
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w34
theorem lc36 : ProvedTranscendental.LogEncloses (⟨9602958969568,9643808094024⟩ : DyadicInterval 40) (⟨2382867281216,2387534528576⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w35
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w36
theorem lc37 : ProvedTranscendental.LogEncloses (⟨6187424241584,6277112521221⟩ : DyadicInterval 40) (⟨1899574315328,1915397646848⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w37
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w38
theorem ew9_ok (x : ℝ) (hx : (⟨95453387776,95453387776⟩ : DyadicInterval 40).Contains x) : (⟨757974801332,757974820661⟩ : DyadicInterval 40).Contains (Reflection.biasE x) := by
  exact ProvedTranscendental.entropy_encloses (c:=(⟨95453387776,95453387776⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (plus:=(⟨91535225664,91535225728⟩ : DyadicInterval 40)) (minus:=(⟨-99853334784,-99853334720⟩ : DyadicInterval 40))
    (lc4 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc5 lc6 (by decide) hx
theorem ew12_ok (x : ℝ) (hx : (⟨95453521152,95453521152⟩ : DyadicInterval 40).Contains x) : (⟨757974789704,757974809033⟩ : DyadicInterval 40).Contains (Reflection.biasE x) := by
  exact ProvedTranscendental.entropy_encloses (c:=(⟨95453521152,95453521152⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (plus:=(⟨91535348416,91535348480⟩ : DyadicInterval 40)) (minus:=(⟨-99853480832,-99853480768⟩ : DyadicInterval 40))
    (lc7 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc8 lc9 (by decide) hx
theorem ew33_ok (x : ℝ) (hx : (⟨92679355392,92679355392⟩ : DyadicInterval 40).Contains x) : (⟨758212709434,758212728763⟩ : DyadicInterval 40).Contains (Reflection.biasE x) := by
  exact ProvedTranscendental.entropy_encloses (c:=(⟨92679355392,92679355392⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (plus:=(⟨88979814784,88979814848⟩ : DyadicInterval 40)) (minus:=(⟨-96819770496,-96819770432⟩ : DyadicInterval 40))
    (lc23 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc24 lc25 (by decide) hx
theorem ew36_ok (x : ℝ) (hx : (⟨98257377536,98257377536⟩ : DyadicInterval 40).Contains x) : (⟨757727157379,757727176708⟩ : DyadicInterval 40).Contains (Reflection.biasE x) := by
  exact ProvedTranscendental.entropy_encloses (c:=(⟨98257377536,98257377536⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (plus:=(⟨94112211456,94112211520⟩ : DyadicInterval 40)) (minus:=(⟨-102928188608,-102928188544⟩ : DyadicInterval 40))
    (lc26 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc27 lc28 (by decide) hx
theorem bw15_ok (x : ℝ) (hx : (⟨95453387776,95453521152⟩ : DyadicInterval 40).Contains x) : (⟨766282438144,766282469088⟩ : DyadicInterval 40).Contains (Reflection.biasB x) := by
  exact ProvedTranscendental.denominator_encloses (c:=(⟨95453387776,95453521152⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (gapLog:=(⟨-8318132416,-8318109056⟩ : DyadicInterval 40))
    (lc10 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc11 (by decide) hx
theorem bw39_ok (x : ℝ) (hx : (⟨92679355392,98257377536⟩ : DyadicInterval 40).Contains x) : (⟨766043361440,766531391424⟩ : DyadicInterval 40).Contains (Reflection.biasB x) := by
  exact ProvedTranscendental.denominator_encloses (c:=(⟨92679355392,98257377536⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (gapLog:=(⟨-8815977088,-7839955648⟩ : DyadicInterval 40))
    (lc29 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc30 (by decide) hx
theorem brcenter28_contact (y : ℝ) (hy : (⟨8730978907165,8730979032346⟩ : DyadicInterval 40).Contains y) : (⟨95453387776,95453521152⟩ : DyadicInterval 40).Contains (Reflection.biasContact y) := by
  exact ProvedTranscendental.contact_bracket (Y:=(⟨8730978907165,8730979032346⟩ : DyadicInterval 40)) (c:=(⟨95453387776,95453521152⟩ : DyadicInterval 40)) (elo:=(⟨757974801332,757974820661⟩ : DyadicInterval 40)) (ehi:=(⟨757974789704,757974809033⟩ : DyadicInterval 40))
    (by decide) (by decide) (by decide) (by decide)
    (ew9_ok _ (DyadicContact.point_contains 40 95453387776)) (ew12_ok _ (DyadicContact.point_contains 40 95453521152))
    (by decide) (by decide) hy
theorem brcenter28_jet (y : ℝ) (hy : (⟨8730978907165,8730979032346⟩ : DyadicInterval 40).Contains y) : (⟨⟨95453387776,95453521152⟩,⟨-11890360848,-11890327137⟩,⟨2946141929,2946154714⟩⟩ : DyadicJetEnclosure 40).Contains reflectionContactJet y := by
  exact ProvedTranscendental.contact_jet (c:=(⟨95453387776,95453521152⟩ : DyadicInterval 40)) (B:=(⟨766282438144,766282469088⟩ : DyadicInterval 40)) (by decide) brcenter28_contact bw15_ok (by decide) (by decide) (by decide) hy
theorem brwhole28_contact (y : ℝ) (hy : (⟨8479061998451,8995132621656⟩ : DyadicInterval 40).Contains y) : (⟨92679355392,98257377536⟩ : DyadicInterval 40).Contains (Reflection.biasContact y) := by
  exact ProvedTranscendental.contact_bracket (Y:=(⟨8479061998451,8995132621656⟩ : DyadicInterval 40)) (c:=(⟨92679355392,98257377536⟩ : DyadicInterval 40)) (elo:=(⟨758212709434,758212728763⟩ : DyadicInterval 40)) (ehi:=(⟨757727157379,757727176708⟩ : DyadicInterval 40))
    (by decide) (by decide) (by decide) (by decide)
    (ew33_ok _ (DyadicContact.point_contains 40 92679355392)) (ew36_ok _ (DyadicContact.point_contains 40 98257377536))
    (by decide) (by decide) hy
theorem brwhole28_jet (y : ℝ) (hy : (⟨8479061998451,8995132621656⟩ : DyadicInterval 40).Contains y) : (⟨⟨92679355392,98257377536⟩,⟨-12603088450,-11205624468⟩,⟨2691008175,3219190823⟩⟩ : DyadicJetEnclosure 40).Contains reflectionContactJet y := by
  exact ProvedTranscendental.contact_jet (c:=(⟨92679355392,98257377536⟩ : DyadicInterval 40)) (B:=(⟨766043361440,766531391424⟩ : DyadicInterval 40)) (by decide) brwhole28_contact bw39_ok (by decide) (by decide) (by decide) hy
noncomputable def centerInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨112742891520,112742891520⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨131211250892,131211250893⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
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
noncomputable def centerStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-112742891520,-112742891520⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes3 := centerStep2.proposed :: centerBoxes2
theorem centerAccepted2 : StepValid centerStep2.shape centerBoxes2 centerStep2.proposed := by
  dsimp only [StepValid,centerStep2]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨437012922368,437012922368⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes4 := centerStep3.proposed :: centerBoxes3
theorem centerAccepted3 : StepValid centerStep3.shape centerBoxes3 centerStep3.proposed := by
  dsimp only [StepValid,centerStep3]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨52151346790,52151346791⟩,⟨-131211250893,-131211250892⟩,⟨437012922368,437012922368⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes5 := centerStep4.proposed :: centerBoxes4
theorem centerAccepted4 : StepValid centerStep4.shape centerBoxes4 centerStep4.proposed := by
  dsimp only [StepValid,centerStep4]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨164894238310,164894238311⟩,⟨968300376883,968300376884⟩,⟨437012922368,437012922368⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes6 := centerStep5.proposed :: centerBoxes5
theorem centerAccepted5 : StepValid centerStep5.shape centerBoxes5 centerStep5.proposed := by
  dsimp only [StepValid,centerStep5]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨52151346790,52151346791⟩,⟨-131211250893,-131211250892⟩,⟨437012922368,437012922368⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes7 := centerStep6.proposed :: centerBoxes6
theorem centerAccepted6 : StepValid centerStep6.shape centerBoxes6 centerStep6.proposed := by
  dsimp only [StepValid,centerStep6]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep7 : Instruction 40 := ⟨.log 7,⟨⟨-2504150381952,-2504150324096⟩,⟨10722856255644,10722856255645⟩,⟨0,0⟩,⟨-104573379102681,-104573379102661⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes8 := centerStep7.proposed :: centerBoxes7
theorem centerAccepted7 : StepValid centerStep7.shape centerBoxes7 centerStep7.proposed := by
  dsimp only [StepValid,centerStep7]
  exact ⟨by decide,by decide,lc0,by decide⟩
noncomputable def centerStep8 : Instruction 40 := ⟨.mul 8 0,⟨⟨-256773232525,-256773226591⟩,⟨-1404638754177,-1404638696319⟩,⟨0,0⟩,⟨10722856255641,10722856255647⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes9 := centerStep8.proposed :: centerBoxes8
theorem centerAccepted8 : StepValid centerStep8.shape centerBoxes8 centerStep8.proposed := by
  dsimp only [StepValid,centerStep8]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep9 : Instruction 40 := ⟨.neg 0,⟨⟨256773226591,256773232525⟩,⟨1404638696319,1404638754177⟩,⟨0,0⟩,⟨-10722856255647,-10722856255641⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes10 := centerStep9.proposed :: centerBoxes9
theorem centerAccepted9 : StepValid centerStep9.shape centerBoxes9 centerStep9.proposed := by
  dsimp only [StepValid,centerStep9]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep10 : Instruction 40 := ⟨.add 12 7,⟨⟨986768736256,986768736256⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes11 := centerStep10.proposed :: centerBoxes10
theorem centerAccepted10 : StepValid centerStep10.shape centerBoxes10 centerStep10.proposed := by
  dsimp only [StepValid,centerStep10]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep11 : Instruction 40 := ⟨.log 0,⟨⟨-118951416704,-118951416640⟩,⟨-1225135916043,-1225135916042⟩,⟨0,0⟩,⟨-1365113360206,-1365113360203⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes12 := centerStep11.proposed :: centerBoxes11
theorem centerAccepted11 : StepValid centerStep11.shape centerBoxes11 centerStep11.proposed := by
  dsimp only [StepValid,centerStep11]
  exact ⟨by decide,by decide,lc1,by decide⟩
noncomputable def centerStep12 : Instruction 40 := ⟨.mul 1 0,⟨⟨-106754249953,-106754249894⟩,⟨-980560211137,-980560211071⟩,⟨0,0⟩,⟨1225135916039,1225135916045⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes13 := centerStep12.proposed :: centerBoxes12
theorem centerAccepted12 : StepValid centerStep12.shape centerBoxes12 centerStep12.proposed := by
  dsimp only [StepValid,centerStep12]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep13 : Instruction 40 := ⟨.neg 0,⟨⟨106754249894,106754249953⟩,⟨980560211071,980560211137⟩,⟨0,0⟩,⟨-1225135916045,-1225135916039⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes14 := centerStep13.proposed :: centerBoxes13
theorem centerAccepted13 : StepValid centerStep13.shape centerBoxes13 centerStep13.proposed := by
  dsimp only [StepValid,centerStep13]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep14 : Instruction 40 := ⟨.add 4 0,⟨⟨363527476485,363527482478⟩,⟨2385198907390,2385198965314⟩,⟨0,0⟩,⟨-11947992171692,-11947992171680⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes15 := centerStep14.proposed :: centerBoxes14
theorem centerAccepted14 : StepValid centerStep14.shape centerBoxes14 centerStep14.proposed := by
  dsimp only [StepValid,centerStep14]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2086122246080,-2086122207360⟩,⟨6456608396192,6456608396240⟩,⟨2913993809326,2913993809346⟩,⟨-37914825936602,-37914825936045⟩,⟨-24443225941371,-24443225941091⟩,⟨-7722846858908,-7722846858810⟩⟩⟩
noncomputable def centerBoxes16 := centerStep15.proposed :: centerBoxes15
theorem centerAccepted15 : StepValid centerStep15.shape centerBoxes15 centerStep15.proposed := by
  dsimp only [StepValid,centerStep15]
  exact ⟨by decide,by decide,lc2,by decide⟩
noncomputable def centerStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-312856662996,-312856657186⟩,⟨-868872515230,-868872481114⟩,⟨-392139181302,-392139165905⟩,⟨5686102980076,5686102980293⟩,⟨3552860205761,3552860244587⟩,⟨1158198711308,1158198711347⟩⟩⟩
noncomputable def centerBoxes17 := centerStep16.proposed :: centerBoxes16
theorem centerAccepted16 : StepValid centerStep16.shape centerBoxes16 centerStep16.proposed := by
  dsimp only [StepValid,centerStep16]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep17 : Instruction 40 := ⟨.neg 0,⟨⟨312856657186,312856662996⟩,⟨868872481114,868872515230⟩,⟨392139165905,392139181302⟩,⟨-5686102980293,-5686102980076⟩,⟨-3552860244587,-3552860205761⟩,⟨-1158198711347,-1158198711308⟩⟩⟩
noncomputable def centerBoxes18 := centerStep17.proposed :: centerBoxes17
theorem centerAccepted17 : StepValid centerStep17.shape centerBoxes17 centerStep17.proposed := by
  dsimp only [StepValid,centerStep17]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-164894238311,-164894238310⟩,⟨-968300376884,-968300376883⟩,⟨-437012922368,-437012922368⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes19 := centerStep18.proposed :: centerBoxes18
theorem centerAccepted18 : StepValid centerStep18.shape centerBoxes18 centerStep18.proposed := by
  dsimp only [StepValid,centerStep18]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨934617389465,934617389466⟩,⟨-968300376884,-968300376883⟩,⟨-437012922368,-437012922368⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes20 := centerStep19.proposed :: centerBoxes19
theorem centerAccepted19 : StepValid centerStep19.shape centerBoxes19 centerStep19.proposed := by
  dsimp only [StepValid,centerStep19]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep20 : Instruction 40 := ⟨.log 0,⟨⟨-178653211200,-178653211136⟩,⟨-1139137293576,-1139137293572⟩,⟨-514114968380,-514114968379⟩,⟨-1180191041946,-1180191041937⟩,⟨760854773284,760854773289⟩,⟨-240392365152,-240392365150⟩⟩⟩
noncomputable def centerBoxes21 := centerStep20.proposed :: centerBoxes20
theorem centerAccepted20 : StepValid centerStep20.shape centerBoxes20 centerStep20.proposed := by
  dsimp only [StepValid,centerStep20]
  exact ⟨by decide,by decide,lc3,by decide⟩
noncomputable def centerStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-151860511207,-151860511151⟩,⟨-810966914189,-810966914125⟩,⟨-366005249584,-366005249556⟩,⟨1003197276695,1003197276714⟩,⟨1373620993216,1373620993290⟩,⟨204340617312,204340617317⟩⟩⟩
noncomputable def centerBoxes22 := centerStep21.proposed :: centerBoxes21
theorem centerAccepted21 : StepValid centerStep21.shape centerBoxes21 centerStep21.proposed := by
  dsimp only [StepValid,centerStep21]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep22 : Instruction 40 := ⟨.neg 0,⟨⟨151860511151,151860511207⟩,⟨810966914125,810966914189⟩,⟨366005249556,366005249584⟩,⟨-1003197276714,-1003197276695⟩,⟨-1373620993290,-1373620993216⟩,⟨-204340617317,-204340617312⟩⟩⟩
noncomputable def centerBoxes23 := centerStep22.proposed :: centerBoxes22
theorem centerAccepted22 : StepValid centerStep22.shape centerBoxes22 centerStep22.proposed := by
  dsimp only [StepValid,centerStep22]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨464717168337,464717174203⟩,⟨1679839395239,1679839429419⟩,⟨758144415461,758144430886⟩,⟨-6689300257007,-6689300256771⟩,⟨-4926481237877,-4926481198977⟩,⟨-1362539328664,-1362539328620⟩⟩⟩
noncomputable def centerBoxes24 := centerStep23.proposed :: centerBoxes23
theorem centerAccepted23 : StepValid centerStep23.shape centerBoxes23 centerStep23.proposed := by
  dsimp only [StepValid,centerStep23]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨828244644822,828244656681⟩,⟨4065038302629,4065038394733⟩,⟨758144415461,758144430886⟩,⟨-18637292428699,-18637292428451⟩,⟨-4926481237877,-4926481198977⟩,⟨-1362539328664,-1362539328620⟩⟩⟩
noncomputable def centerBoxes25 := centerStep24.proposed :: centerBoxes24
theorem centerAccepted24 : StepValid centerStep24.shape centerBoxes24 centerStep24.proposed := by
  dsimp only [StepValid,centerStep24]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨104302693580,104302693582⟩,⟨-262422501786,-262422501784⟩,⟨874025844736,874025844736⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes26 := centerStep25.proposed :: centerBoxes25
theorem centerAccepted25 : StepValid centerStep25.shape centerBoxes25 centerStep25.proposed := by
  dsimp only [StepValid,centerStep25]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep26 : Instruction 40 := ⟨.inv 0,⟨⟨11590552248434,11590552248657⟩,⟨29161487720360,29161487721706⟩,⟨-97125413279183,-97125413275443⟩,⟨146738886609938,146738886620647⟩,⟨-244364676175784,-244364676134436⟩,⟨1627764700374885,1627764700468861⟩⟩⟩
noncomputable def centerBoxes27 := centerStep26.proposed :: centerBoxes26
theorem centerAccepted26 : StepValid centerStep26.shape centerBoxes26 centerStep26.proposed := by
  dsimp only [StepValid,centerStep26]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨8730978907165,8730979032346⟩,⟨64818673197748,64818674485034⟩,⟨-65171018029249,-65171016816108⟩,⟨129697868436146,129697874928849⟩,⟨-574986452680863,-574986441043131⟩,⟨1077864572367459,1077864592725864⟩⟩⟩
noncomputable def centerBoxes28 := centerStep27.proposed :: centerBoxes27
theorem centerAccepted27 : StepValid centerStep27.shape centerBoxes27 centerStep27.proposed := by
  dsimp only [StepValid,centerStep27]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep28 : Instruction 40 := ⟨.contact 0,⟨⟨95453387776,95453521152⟩,⟨-700963418528,-700961417267⟩,⟨704771727936,704773739198⟩,⟨8836341831428,8836390717504⟩,⟨-4076613025257,-4076550200083⟩,⟨-1305725095922,-1305646526121⟩⟩⟩
noncomputable def centerBoxes29 := centerStep28.proposed :: centerBoxes28
theorem centerAccepted28 : StepValid centerStep28.shape centerBoxes28 centerStep28.proposed := by
  dsimp only [StepValid,centerStep28]
  exact ⟨by decide,by decide,(⟨⟨95453387776,95453521152⟩,⟨-11890360848,-11890327137⟩,⟨2946141929,2946154714⟩⟩ : DyadicJetEnclosure 40),brcenter28_jet,by decide⟩
noncomputable def centerStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes30 := centerStep29.proposed :: centerBoxes29
theorem centerAccepted29 : StepValid centerStep29.shape centerBoxes29 centerStep29.proposed := by
  dsimp only [StepValid,centerStep29]
  exact ⟨by decide,by decide,lc4,by decide⟩
noncomputable def centerStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1194965015552,1194965148928⟩,⟨-700963418528,-700961417267⟩,⟨704771727936,704773739198⟩,⟨8836341831428,8836390717504⟩,⟨-4076613025257,-4076550200083⟩,⟨-1305725095922,-1305646526121⟩⟩⟩
noncomputable def centerBoxes31 := centerStep30.proposed :: centerBoxes30
theorem centerAccepted30 : StepValid centerStep30.shape centerBoxes30 centerStep30.proposed := by
  dsimp only [StepValid,centerStep30]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep31 : Instruction 40 := ⟨.log 0,⟨⟨91535225664,91535348480⟩,⟨-644970705659,-644968792268⟩,⟨648474736261,648476659245⟩,⟨7752158862383,7752206995729⟩,⟨-3370582110222,-3370521628331⟩,⟨-1583886742234,-1583812046174⟩⟩⟩
noncomputable def centerBoxes32 := centerStep31.proposed :: centerBoxes31
theorem centerAccepted31 : StepValid centerStep31.shape centerBoxes31 centerStep31.proposed := by
  dsimp only [StepValid,centerStep31]
  exact ⟨by decide,by decide,lc13,by decide⟩
noncomputable def centerStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨99481796823,99481941406⟩,⟨-759319342369,-759316939724⟩,⟨763444461389,763446876143⟩,⟨9983151955178,9983215051929⟩,⟨-4829416119722,-4829339480141⟩,⟨-998767188957,-998674291582⟩⟩⟩
noncomputable def centerBoxes33 := centerStep32.proposed :: centerBoxes32
theorem centerAccepted32 : StepValid centerStep32.shape centerBoxes32 centerStep32.proposed := by
  dsimp only [StepValid,centerStep32]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-95453521152,-95453387776⟩,⟨700961417267,700963418528⟩,⟨-704773739198,-704771727936⟩,⟨-8836390717504,-8836341831428⟩,⟨4076550200083,4076613025257⟩,⟨1305646526121,1305725095922⟩⟩⟩
noncomputable def centerBoxes34 := centerStep33.proposed :: centerBoxes33
theorem centerAccepted33 : StepValid centerStep33.shape centerBoxes33 centerStep33.proposed := by
  dsimp only [StepValid,centerStep33]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1004058106624,1004058240000⟩,⟨700961417267,700963418528⟩,⟨-704773739198,-704771727936⟩,⟨-8836390717504,-8836341831428⟩,⟨4076550200083,4076613025257⟩,⟨1305646526121,1305725095922⟩⟩⟩
noncomputable def centerBoxes35 := centerStep34.proposed :: centerBoxes34
theorem centerAccepted34 : StepValid centerStep34.shape centerBoxes34 centerStep34.proposed := by
  dsimp only [StepValid,centerStep34]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep35 : Instruction 40 := ⟨.log 0,⟨⟨-99853480832,-99853334720⟩,⟨767600123382,767602416866⟩,⟨-771774976058,-771772671068⟩,⟨-10212332820209,-10212274798957⟩,⟨5002894265896,5002966875752⟩,⟨888042838317,888132303355⟩⟩⟩
noncomputable def centerBoxes36 := centerStep35.proposed :: centerBoxes35
theorem centerAccepted35 : StepValid centerStep35.shape centerBoxes35 centerStep35.proposed := by
  dsimp only [StepValid,centerStep35]
  exact ⟨by decide,by decide,lc14,by decide⟩
noncomputable def centerStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-91184765754,-91184620213⟩,⟨637302481891,637304944281⟩,⟨-640769227982,-640766753165⟩,⟨-7544551934553,-7544486379116⟩,⟨3214300243210,3214379152065⟩,⟨1681758051679,1681852944956⟩⟩⟩
noncomputable def centerBoxes37 := centerStep36.proposed :: centerBoxes36
theorem centerAccepted36 : StepValid centerStep36.shape centerBoxes36 centerStep36.proposed := by
  dsimp only [StepValid,centerStep36]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨8297031069,8297321193⟩,⟨-122016860478,-122011995443⟩,⟨122675233407,122680122978⟩,⟨2438600020625,2438728672813⟩,⟨-1615115876512,-1614960328076⟩,⟨682990862722,683178653374⟩⟩⟩
noncomputable def centerBoxes38 := centerStep37.proposed :: centerBoxes37
theorem centerAccepted37 : StepValid centerStep37.shape centerBoxes37 centerStep37.proposed := by
  dsimp only [StepValid,centerStep37]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨4148515534,4148660597⟩,⟨-61008430239,-61005997721⟩,⟨61337616703,61340061489⟩,⟨1219300010312,1219364336407⟩,⟨-807557938256,-807480164038⟩,⟨341495431361,341589326687⟩⟩⟩
noncomputable def centerBoxes39 := centerStep38.proposed :: centerBoxes38
theorem centerAccepted38 : StepValid centerStep38.shape centerBoxes38 centerStep38.proposed := by
  dsimp only [StepValid,centerStep38]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-4148660597,-4148515534⟩,⟨61005997721,61008430239⟩,⟨-61340061489,-61337616703⟩,⟨-1219364336407,-1219300010312⟩,⟨807480164038,807557938256⟩,⟨-341589326687,-341495431361⟩⟩⟩
noncomputable def centerBoxes40 := centerStep39.proposed :: centerBoxes39
theorem centerAccepted39 : StepValid centerStep39.shape centerBoxes39 centerStep39.proposed := by
  dsimp only [StepValid,centerStep39]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨757974723019,757974887346⟩,⟨61005997721,61008430239⟩,⟨-61340061489,-61337616703⟩,⟨-1219364336407,-1219300010312⟩,⟨807480164038,807557938256⟩,⟨-341589326687,-341495431361⟩⟩⟩
noncomputable def centerBoxes41 := centerStep40.proposed :: centerBoxes40
theorem centerAccepted40 : StepValid centerStep40.shape centerBoxes40 centerStep40.proposed := by
  dsimp only [StepValid,centerStep40]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨8286723857,8286747016⟩,⟨-121707537796,-121707020258⟩,⟨122368599550,122369119750⟩,⟨2427997372892,2428013108102⟩,⟨-1606436266508,-1606419239214⟩,⟨676786167669,676805283197⟩⟩⟩
noncomputable def centerBoxes42 := centerStep41.proposed :: centerBoxes41
theorem centerAccepted41 : StepValid centerStep41.shape centerBoxes41 centerStep41.proposed := by
  dsimp only [StepValid,centerStep41]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-8286747016,-8286723857⟩,⟨121707020258,121707537796⟩,⟨-122369119750,-122368599550⟩,⟨-2428013108102,-2427997372892⟩,⟨1606419239214,1606436266508⟩,⟨-676805283197,-676786167669⟩⟩⟩
noncomputable def centerBoxes43 := centerStep42.proposed :: centerBoxes42
theorem centerAccepted42 : StepValid centerStep42.shape centerBoxes42 centerStep42.proposed := by
  dsimp only [StepValid,centerStep42]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1091224880760,1091224903919⟩,⟨121707020258,121707537796⟩,⟨-122369119750,-122368599550⟩,⟨-2428013108102,-2427997372892⟩,⟨1606419239214,1606436266508⟩,⟨-676805283197,-676786167669⟩⟩⟩
noncomputable def centerBoxes44 := centerStep43.proposed :: centerBoxes43
theorem centerAccepted43 : StepValid centerStep43.shape centerBoxes43 centerStep43.proposed := by
  dsimp only [StepValid,centerStep43]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep44 : Instruction 40 := ⟨.log 0,⟨⟨-8318132416,-8318109056⟩,⟨122631259124,122631783196⟩,⟨-123298389194,-123297862426⟩,⟨-2460128892287,-2460112868757⟩,⟨1632370047310,1632387355785⟩,⟨-695771520019,-695752126710⟩⟩⟩
noncomputable def centerBoxes45 := centerStep44.proposed :: centerBoxes44
theorem centerAccepted44 : StepValid centerStep44.shape centerBoxes44 centerStep44.proposed := by
  dsimp only [StepValid,centerStep44]
  exact ⟨by decide,by decide,lc11,by decide⟩
noncomputable def centerStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-4159066208,-4159054528⟩,⟨61315629562,61315891598⟩,⟨-61649194597,-61648931213⟩,⟨-1230064446144,-1230056434378⟩,⟨816185023655,816193677893⟩,⟨-347885760010,-347876063355⟩⟩⟩
noncomputable def centerBoxes46 := centerStep45.proposed :: centerBoxes45
theorem centerAccepted45 : StepValid centerStep45.shape centerBoxes45 centerStep45.proposed := by
  dsimp only [StepValid,centerStep45]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep46 : Instruction 40 := ⟨.neg 0,⟨⟨4159054528,4159066208⟩,⟨-61315891598,-61315629562⟩,⟨61648931213,61649194597⟩,⟨1230056434378,1230064446144⟩,⟨-816193677893,-816185023655⟩,⟨347876063355,347885760010⟩⟩⟩
noncomputable def centerBoxes47 := centerStep46.proposed :: centerBoxes46
theorem centerAccepted46 : StepValid centerStep46.shape centerBoxes46 centerStep46.proposed := by
  dsimp only [StepValid,centerStep46]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨766282438144,766282469088⟩,⟨-61315891598,-61315629562⟩,⟨61648931213,61649194597⟩,⟨1230056434378,1230064446144⟩,⟨-816193677893,-816185023655⟩,⟨347876063355,347885760010⟩⟩⟩
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
noncomputable def centerStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272806220190,272806225980⟩,⟨30426755064,30426884449⟩,⟨-30592279938,-30592149887⟩,⟨-607003277026,-606999343223⟩,⟨401604809803,401609066627⟩,⟨-169201320800,-169196541917⟩⟩⟩
noncomputable def centerBoxes51 := centerStep50.proposed :: centerBoxes50
theorem centerAccepted50 : StepValid centerStep50.shape centerBoxes50 centerStep50.proposed := by
  dsimp only [StepValid,centerStep50]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1532564876288,1532564938176⟩,⟨-122631783196,-122631259124⟩,⟨123297862426,123298389194⟩,⟨2460112868756,2460128892288⟩,⟨-1632387355786,-1632370047310⟩,⟨695752126710,695771520020⟩⟩⟩
noncomputable def centerBoxes52 := centerStep51.proposed :: centerBoxes51
theorem centerAccepted51 : StepValid centerStep51.shape centerBoxes51 centerStep51.proposed := by
  dsimp only [StepValid,centerStep51]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1204039538199,1204039698141⟩,⟨-840576633250,-840574010070⟩,⟨845143231770,845145868157⟩,⟨11769959516402,11770028123832⟩,⟨-6068609525656,-6068525681758⟩,⟨-379339496854,-379237617508⟩⟩⟩
noncomputable def centerBoxes53 := centerStep52.proposed :: centerBoxes52
theorem centerAccepted52 : StepValid centerStep52.shape centerBoxes52 centerStep52.proposed := by
  dsimp only [StepValid,centerStep52]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1308567448622,1308567768506⟩,⟨-1681153266500,-1681148020140⟩,⟨1690286463540,1690291736314⟩,⟨23539919032807,23540056247656⟩,⟨-12137219051308,-12137051363516⟩,⟨-758678849786,-758475378940⟩⟩⟩
noncomputable def centerBoxes54 := centerStep53.proposed :: centerBoxes53
theorem centerAccepted53 : StepValid centerStep53.shape centerBoxes53 centerStep53.proposed := by
  dsimp only [StepValid,centerStep53]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep54 : Instruction 40 := ⟨.log 0,⟨⟨191388560448,191388829248⟩,⟨-1412573395845,-1412568642329⟩,⟨1420247132523,1420251910110⟩,⟨17964420567364,17964552909924⟩,⟨-8373560274673,-8373404605548⟩,⟨-2472028696451,-2471845233663⟩⟩⟩
noncomputable def centerBoxes55 := centerStep54.proposed :: centerBoxes54
theorem centerAccepted54 : StepValid centerStep54.shape centerBoxes54 centerStep54.proposed := by
  dsimp only [StepValid,centerStep54]
  exact ⟨by decide,by decide,lc16,by decide⟩
noncomputable def centerStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨65803083235,65803189448⟩,⟨-477929860641,-477928157682⟩,⟨480526096377,480527807905⟩,⟨5907897300003,5907941377425⟩,⟨-2662002749449,-2661948639199⟩,⟨-1008424501837,-1008358591254⟩⟩⟩
noncomputable def centerBoxes56 := centerStep55.proposed :: centerBoxes55
theorem centerAccepted55 : StepValid centerStep55.shape centerBoxes55 centerStep55.proposed := by
  dsimp only [StepValid,centerStep55]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380253578529,380253601955⟩,⟨11983740616,11984053351⟩,⟨-12049196636,-12048882291⟩,⟨-242471699456,-242462135604⟩,⟨161583647698,161593964996⟩,⟨-70076986550,-70065442000⟩⟩⟩
noncomputable def centerBoxes57 := centerStep56.proposed :: centerBoxes56
theorem centerAccepted56 : StepValid centerStep56.shape centerBoxes56 centerStep56.proposed := by
  dsimp only [StepValid,centerStep56]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3179261980423,3179262176286⟩,⟨-100197472658,-100194845565⟩,⟨100739488534,100742129155⟩,⟨2033516746515,2033597289493⟩,⟨-1357420963469,-1357334202571⟩,⟨592194238826,592291168135⟩⟩⟩
noncomputable def centerBoxes58 := centerStep57.proposed :: centerBoxes57
theorem centerAccepted57 : StepValid centerStep57.shape centerBoxes57 centerStep57.proposed := by
  dsimp only [StepValid,centerStep57]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨190271058021,190271376861⟩,⟨-1387941340118,-1387936163932⟩,⟨1395480756183,1395485958471⟩,⟨17291619604087,17291755718318⟩,⟨-7866058355791,-7865893489115⟩,⟨-2792386806679,-2792187565216⟩⟩⟩
noncomputable def centerBoxes59 := centerStep58.proposed :: centerBoxes58
theorem centerAccepted58 : StepValid centerStep58.shape centerBoxes58 centerStep58.proposed := by
  dsimp only [StepValid,centerStep58]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨381659618469,381660206109⟩,⟨-2800514735963,-2800504806261⟩,⟨2815727888706,2815737868581⟩,⟨35256040171451,35256308628242⟩,⟨-16239618630464,-16239298094663⟩,⟨-5264415503130,-5264032798879⟩⟩⟩
noncomputable def centerBoxes60 := centerStep59.proposed :: centerBoxes59
theorem centerAccepted59 : StepValid centerStep59.shape centerBoxes59 centerStep59.proposed := by
  dsimp only [StepValid,centerStep59]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨522528062661,522528289228⟩,⟨84111896694,84115268762⟩,⟨-84572504780,-84569115698⟩,⟨-1674426700928,-1674337107093⟩,⟨1106504519734,1106612534880⟩,⟨-464122109755,-463992004104⟩⟩⟩
noncomputable def centerBoxes61 := centerStep60.proposed :: centerBoxes60
theorem centerAccepted60 : StepValid centerStep60.shape centerBoxes60 centerStep60.proposed := by
  dsimp only [StepValid,centerStep60]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨360217257880,360217492165⟩,⟨86976831333,86980337116⟩,⟨-87453147148,-87449623670⟩,⟨-1724459334854,-1724365753186⟩,⟨1137154168735,1137266674808⟩,⟨-472853984632,-472718776711⟩⟩⟩
noncomputable def centerBoxes62 := centerStep61.proposed :: centerBoxes61
theorem centerAccepted61 : StepValid centerStep61.shape centerBoxes61 centerStep61.proposed := by
  dsimp only [StepValid,centerStep61]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨720434515760,720434984330⟩,⟨173953662666,173960674232⟩,⟨-174906294296,-174899247340⟩,⟨-3448918669708,-3448731506372⟩,⟨2274308337470,2274533349616⟩,⟨-945707969264,-945437553422⟩⟩⟩
noncomputable def centerBoxes63 := centerStep62.proposed :: centerBoxes62
theorem centerAccepted62 : StepValid centerStep62.shape centerBoxes62 centerStep62.proposed := by
  dsimp only [StepValid,centerStep62]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1524278129272,1524278214319⟩,⟨-924762938,-923721328⟩,⟨928742676,929789644⟩,⟨32099760654,32131519396⟩,⟨-25968116572,-25933780802⟩,⟨18946843513,18985352351⟩⟩⟩
noncomputable def centerBoxes64 := centerStep63.proposed :: centerBoxes63
theorem centerAccepted63 : StepValid centerStep63.shape centerBoxes63 centerStep63.proposed := by
  dsimp only [StepValid,centerStep63]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨998754854613,998755559929⟩,⟨240550008980,240560425622⟩,⟨-241868070283,-241857600993⟩,⟨-4760574993671,-4760294093682⟩,⟨3136204427141,3136539394691⟩,⟨-1298937919954,-1298537377842⟩⟩⟩
noncomputable def centerBoxes65 := centerStep64.proposed :: centerBoxes64
theorem centerAccepted64 : StepValid centerStep64.shape centerBoxes64 centerStep64.proposed := by
  dsimp only [StepValid,centerStep64]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67687536806,67687539680⟩,⟨15098718070,15098782598⟩,⟨-15180857070,-15180792212⟩,⟨-299530230659,-299528257864⟩,⟨197595841026,197597972028⟩,⟨-82260692806,-82258305113⟩⟩⟩
noncomputable def centerBoxes66 := centerStep65.proposed :: centerBoxes65
theorem centerAccepted65 : StepValid centerStep65.shape centerBoxes65 centerStep65.proposed := by
  dsimp only [StepValid,centerStep65]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50987946343,50987949239⟩,⟨261623301513,261623366582⟩,⟨35236975484,35237027437⟩,⟨-1261326405532,-1261324387827⟩,⟨-200150184513,-200148276090⟩,⟨-166780845243,-166778952308⟩⟩⟩
noncomputable def centerBoxes67 := centerStep66.proposed :: centerBoxes66
theorem centerAccepted66 : StepValid centerStep66.shape centerBoxes66 centerStep66.proposed := by
  dsimp only [StepValid,centerStep66]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2136180319240,2136180491768⟩,⟨-341862998962,-341861524190⟩,⟨343719827060,343721309424⟩,⟨6885458788152,6885503968016⟩,⟨-4578141539846,-4578092869864⟩,⟨1967214547907,1967268925623⟩⟩⟩
noncomputable def centerBoxes68 := centerStep67.proposed :: centerBoxes67
theorem centerAccepted67 : StepValid centerStep67.shape centerBoxes67 centerStep67.proposed := by
  dsimp only [StepValid,centerStep67]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2977535520299,2977535881018⟩,⟨-714763581349,-714760469046⟩,⟨718645789087,718648917419⟩,⟨14453237606640,14453333140717⟩,⟨-9629434811914,-9629332172948⟩,⟨4170847896868,4170962251679⟩⟩⟩
noncomputable def centerBoxes69 := centerStep68.proposed :: centerBoxes68
theorem centerAccepted68 : StepValid centerStep68.shape centerBoxes68 centerStep68.proposed := by
  dsimp only [StepValid,centerStep68]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨138078049843,138078074414⟩,⟨675343784667,675344192921⟩,⟨128749542514,128749841730⟩,⟨-3085643980288,-3085632068419⟩,⟨-840474194174,-840463254912⟩,⟨-212173448840,-212162685535⟩⟩⟩
noncomputable def centerBoxes70 := centerStep69.proposed :: centerBoxes69
theorem centerAccepted69 : StepValid centerStep69.shape centerBoxes69 centerStep69.proposed := by
  dsimp only [StepValid,centerStep69]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8755378612754,8755380170775⟩,⟨-42822846657178,-42822805529579⟩,⟨-8163888558356,-8163866679868⟩,⟨614551647621089,614553202656879⟩,⟨133152256990020,133153246107579⟩,⟨28677636594508,28678402764385⟩⟩⟩
noncomputable def centerBoxes71 := centerStep70.proposed :: centerBoxes70
theorem centerAccepted70 : StepValid centerStep70.shape centerBoxes70 centerStep70.proposed := by
  dsimp only [StepValid,centerStep70]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨7953055404380,7953062436040⟩,⟨-36983192137016,-36983044019917⟩,⟨-9341762047188,-9341653227236⟩,⟨501588904748597,501593784445607⟩,⟨153557478138208,153561632737834⟩,⟨19297858562091,19301929358540⟩⟩⟩
noncomputable def centerBoxes72 := centerStep71.proposed :: centerBoxes71
theorem centerAccepted71 : StepValid centerStep71.shape centerBoxes71 centerStep71.proposed := by
  dsimp only [StepValid,centerStep71]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨15906110808760,15906124872080⟩,⟨-73966384274032,-73966088039834⟩,⟨-18683524094376,-18683306454472⟩,⟨1003177809497194,1003187568891214⟩,⟨307114956276416,307123265475668⟩,⟨38595717124182,38603858717080⟩⟩⟩
noncomputable def centerBoxes73 := centerStep72.proposed :: centerBoxes72
theorem centerAccepted72 : StepValid centerStep72.shape centerBoxes72 centerStep72.proposed := by
  dsimp only [StepValid,centerStep72]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10722856255644,10722856255645⟩,⟨-104573379102681,-104573379102661⟩,⟨0,0⟩,⟨2039678860973798,2039678860974382⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes74 := centerStep73.proposed :: centerBoxes73
theorem centerAccepted73 : StepValid centerStep73.shape centerBoxes73 centerStep73.proposed := by
  dsimp only [StepValid,centerStep73]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9623344627868,9623344627869⟩,⟨-104573379102680,-104573379102661⟩,⟨0,0⟩,⟨2039678860973798,2039678860974364⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes75 := centerStep74.proposed :: centerBoxes74
theorem centerAccepted74 : StepValid centerStep74.shape centerBoxes74 centerStep74.proposed := by
  dsimp only [StepValid,centerStep74]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep75 : Instruction 40 := ⟨.log 0,⟨⟨2385198907456,2385198965312⟩,⟨-11947992171781,-11947992171683⟩,⟨0,0⟩,⟨103208265737483,103208265748560⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes76 := centerStep75.proposed :: centerBoxes75
theorem centerAccepted75 : StepValid centerStep75.shape centerBoxes75 centerStep75.proposed := by
  dsimp only [StepValid,centerStep75]
  exact ⟨by decide,by decide,lc17,by decide⟩
noncomputable def centerStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7331522507987,7331522508033⟩,⟨-43052541316309,-43052541315722⟩,⟨-19430454996367,-19430454996122⟩,⟨505630668588361,505630668598942⟩,⟨277087474409863,277087474415018⟩,⟨102991590340213,102991590342157⟩⟩⟩
noncomputable def centerBoxes77 := centerStep76.proposed :: centerBoxes76
theorem centerAccepted76 : StepValid centerStep76.shape centerBoxes76 centerStep76.proposed := by
  dsimp only [StepValid,centerStep76]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6232010880211,6232010880257⟩,⟨-43052541316309,-43052541315722⟩,⟨-19430454996368,-19430454996121⟩,⟨505630668588369,505630668598937⟩,⟨277087474409867,277087474415017⟩,⟨102991590340214,102991590342157⟩⟩⟩
noncomputable def centerBoxes78 := centerStep77.proposed :: centerBoxes77
theorem centerAccepted77 : StepValid centerStep77.shape centerBoxes77 centerStep77.proposed := by
  dsimp only [StepValid,centerStep77]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep78 : Instruction 40 := ⟨.log 0,⟨⟨1907468996160,1907469034752⟩,⟨-7595745689884,-7595745689701⟩,⟨-3428108777757,-3428108777677⟩,⟨36734634891594,36734634897405⟩,⟨25204080713194,25204080715952⟩,⟨7482454493163,7482454494291⟩⟩⟩
noncomputable def centerBoxes79 := centerStep78.proposed :: centerBoxes78
theorem centerAccepted78 : StepValid centerStep78.shape centerBoxes78 centerStep78.proposed := by
  dsimp only [StepValid,centerStep78]
  exact ⟨by decide,by decide,lc18,by decide⟩
noncomputable def centerStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨101182341120,101182341120⟩,⟨874025844736,874025844736⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes80 := centerStep79.proposed :: centerBoxes79
theorem centerAccepted79 : StepValid centerStep79.shape centerBoxes79 centerStep79.proposed := by
  dsimp only [StepValid,centerStep79]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨140164977480,140164977482⟩,⟨677867517295,677867517299⟩,⟨305934885272,305934885274⟩,⟨-1705494687256,-1705494687251⟩,⟨-1539446302312,-1539446302308⟩,⟨-347391131648,-347391131648⟩⟩⟩
noncomputable def centerBoxes81 := centerStep80.proposed :: centerBoxes80
theorem centerAccepted80 : StepValid centerStep80.shape centerBoxes80 centerStep80.proposed := by
  dsimp only [StepValid,centerStep80]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4292667903616,4292668000064⟩,⟨-19543737861665,-19543737861384⟩,⟨-3428108777757,-3428108777677⟩,⟨139942900629077,139942900645965⟩,⟨25204080713194,25204080715952⟩,⟨7482454493163,7482454494291⟩⟩⟩
noncomputable def centerBoxes82 := centerStep81.proposed :: centerBoxes81
theorem centerAccepted81 : StepValid centerStep81.shape centerBoxes81 centerStep81.proposed := by
  dsimp only [StepValid,centerStep81]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨763319236938,763320412218⟩,⟨-5601029471926,-5601009612522⟩,⟨5631455777412,5631475737162⟩,⟨70512080342902,70512617256484⟩,⟨-32479237260928,-32478596189326⟩,⟨-10528831006260,-10528065597758⟩⟩⟩
noncomputable def centerBoxes83 := centerStep82.proposed :: centerBoxes82
theorem centerAccepted82 : StepValid centerStep82.shape centerBoxes82 centerStep82.proposed := by
  dsimp only [StepValid,centerStep82]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5055987140554,5055988412282⟩,⟨-25144767333591,-25144747473906⟩,⟨2203346999655,2203366959485⟩,⟨210454980971979,210455517902449⟩,⟨-7275156547734,-7274515473374⟩,⟨-3046376513097,-3045611103467⟩⟩⟩
noncomputable def centerBoxes84 := centerStep83.proposed :: centerBoxes83
theorem centerAccepted83 : StepValid centerStep83.shape centerBoxes83 centerStep83.proposed := by
  dsimp only [StepValid,centerStep83]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨465276221397,465276338428⟩,⟨1705172513326,1705175351836⟩,⟨202762573939,202764410740⟩,⟨-30721149816749,-30721066288575⟩,⟨1081993878965,1082068740214⟩,⟨-280342198974,-280271762303⟩⟩⟩
noncomputable def centerBoxes85 := centerStep84.proposed :: centerBoxes84
theorem centerAccepted84 : StepValid centerStep84.shape centerBoxes84 centerStep84.proposed := by
  dsimp only [StepValid,centerStep84]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep85 : Instruction 40 := ⟨.mul 88 85,⟨⟨225485783040,225485783040⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes86 := centerStep85.proposed :: centerBoxes85
theorem centerAccepted85 : StepValid centerStep85.shape centerBoxes85 centerStep85.proposed := by
  dsimp only [StepValid,centerStep85]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep86 : Instruction 40 := ⟨.neg 0,⟨⟨-225485783040,-225485783040⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes87 := centerStep86.proposed :: centerBoxes86
theorem centerAccepted86 : StepValid centerStep86.shape centerBoxes86 centerStep86.proposed := by
  dsimp only [StepValid,centerStep86]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep87 : Instruction 40 := ⟨.add 89 0,⟨⟨874025844736,874025844736⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes88 := centerStep87.proposed :: centerBoxes87
theorem centerAccepted87 : StepValid centerStep87.shape centerBoxes87 centerStep87.proposed := by
  dsimp only [StepValid,centerStep87]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep88 : Instruction 40 := ⟨.mul 12 0,⟨⟨1896046787762,1896046833754⟩,⟨-14268118270302,-14268118154511⟩,⟨0,0⟩,⟨129834476802270,129834476811468⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes89 := centerStep88.proposed :: centerBoxes88
theorem centerAccepted88 : StepValid centerStep88.shape centerBoxes88 centerStep88.proposed := by
  dsimp only [StepValid,centerStep88]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep89 : Instruction 40 := ⟨.neg 91,⟨⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes90 := centerStep89.proposed :: centerBoxes89
theorem centerAccepted89 : StepValid centerStep89.shape centerBoxes89 centerStep89.proposed := by
  dsimp only [StepValid,centerStep89]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep90 : Instruction 40 := ⟨.add 1 0,⟨⟨796535159986,796535205978⟩,⟨-14268118270302,-14268118154511⟩,⟨0,0⟩,⟨129834476802270,129834476811468⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes91 := centerStep90.proposed :: centerBoxes90
theorem centerAccepted90 : StepValid centerStep90.shape centerBoxes90 centerStep90.proposed := by
  dsimp only [StepValid,centerStep90]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨37780756755,37780758938⟩,⟨-771811723760,-771811712764⟩,⟨316591611439,316591629720⟩,⟨9563626087464,9563626115682⟩,⟨-6467554870054,-6467554778038⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes92 := centerStep91.proposed :: centerBoxes91
theorem centerAccepted91 : StepValid centerStep91.shape centerBoxes91 centerStep91.proposed := by
  dsimp only [StepValid,centerStep91]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨503056978152,503057097366⟩,⟨933360789566,933363639072⟩,⟨519354185378,519356040460⟩,⟨-21157523729285,-21157440172893⟩,⟨-5385560991089,-5385486037824⟩,⟨-280342198974,-280271762303⟩⟩⟩
noncomputable def centerBoxes93 := centerStep92.proposed :: centerBoxes92
theorem centerAccepted92 : StepValid centerStep92.shape centerBoxes92 centerStep92.proposed := by
  dsimp only [StepValid,centerStep92]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep93 : Instruction 40 := ⟨.inv 17,⟨⟨506844853278,506844865574⟩,⟨2538898610666,2538898733883⟩,⟨0,0⟩,⟨3504487769187,3504490687699⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes94 := centerStep93.proposed :: centerBoxes93
theorem centerAccepted93 : StepValid centerStep93.shape centerBoxes93 centerStep93.proposed := by
  dsimp only [StepValid,centerStep93]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨231895537837,231895598418⟩,⟨1591870182308,1591871837946⟩,⟨239408105596,239408966547⟩,⟨-3839166692663,-3839112854695⟩,⟨-1283348244097,-1283309290659⟩,⟨-129230105953,-129197633434⟩⟩⟩
noncomputable def centerBoxes95 := centerStep94.proposed :: centerBoxes94
theorem centerAccepted94 : StepValid centerStep94.shape centerBoxes94 centerStep94.proposed := by
  dsimp only [StepValid,centerStep94]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-763320412218,-763319236938⟩,⟨5601009612522,5601029471926⟩,⟨-5631475737162,-5631455777412⟩,⟨-70512617256484,-70512080342902⟩,⟨32478596189326,32479237260928⟩,⟨10528065597758,10528831006260⟩⟩⟩
noncomputable def centerBoxes96 := centerStep95.proposed :: centerBoxes95
theorem centerAccepted95 : StepValid centerStep95.shape centerBoxes95 centerStep95.proposed := by
  dsimp only [StepValid,centerStep95]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3529347491398,3529348763126⟩,⟨-13942728249143,-13942708389458⟩,⟨-9059584514919,-9059564555089⟩,⟨69430283372593,69430820303063⟩,⟨57682676902520,57683317976880⟩,⟨18010520090921,18011285500551⟩⟩⟩
noncomputable def centerBoxes97 := centerStep96.proposed :: centerBoxes96
theorem centerAccepted96 : StepValid centerStep96.shape centerBoxes96 centerStep96.proposed := by
  dsimp only [StepValid,centerStep96]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨449918763161,449918925288⟩,⟨398493130511,398496446291⟩,⟨-172882155007,-172879256663⟩,⟨-13815439729005,-13815344820945⟩,⟨-7053055764240,-7052954428323⟩,⟨-3860719713212,-3860610629962⟩⟩⟩
noncomputable def centerBoxes98 := centerStep97.proposed :: centerBoxes97
theorem centerAccepted97 : StepValid centerStep97.shape centerBoxes97 centerStep97.proposed := by
  dsimp only [StepValid,centerStep97]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨329788476620,329788476622⟩,⟨1936600753766,1936600753768⟩,⟨874025844736,874025844736⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes99 := centerStep98.proposed :: centerBoxes98
theorem centerAccepted98 : StepValid centerStep98.shape centerBoxes98 centerStep98.proposed := by
  dsimp only [StepValid,centerStep98]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-329788476622,-329788476620⟩,⟨-1936600753768,-1936600753766⟩,⟨-874025844736,-874025844736⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes100 := centerStep99.proposed :: centerBoxes99
theorem centerAccepted99 : StepValid centerStep99.shape centerBoxes99 centerStep99.proposed := by
  dsimp only [StepValid,centerStep99]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨769723151154,769723151156⟩,⟨-1936600753768,-1936600753766⟩,⟨-874025844736,-874025844736⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes101 := centerStep100.proposed :: centerBoxes100
theorem centerAccepted100 : StepValid centerStep100.shape centerBoxes100 centerStep100.proposed := by
  dsimp only [StepValid,centerStep100]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1335341081769,1335341108790⟩,⟨-8677149961194,-8677149893073⟩,⟨-3916167702599,-3916167671857⟩,⟨52473617489730,52473617494539⟩,⟨33535333564923,33535333644379⟩,⟨10688317880844,10688317881777⟩⟩⟩
noncomputable def centerBoxes102 := centerStep101.proposed :: centerBoxes101
theorem centerAccepted101 : StepValid centerStep101.shape centerBoxes101 centerStep101.proposed := by
  dsimp only [StepValid,centerStep101]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1335341108790,-1335341081769⟩,⟨8677149893073,8677149961194⟩,⟨3916167671857,3916167702599⟩,⟨-52473617494539,-52473617489730⟩,⟨-33535333644379,-33535333564923⟩,⟨-10688317881777,-10688317880844⟩⟩⟩
noncomputable def centerBoxes103 := centerStep102.proposed :: centerBoxes102
theorem centerAccepted102 : StepValid centerStep102.shape centerBoxes102 centerStep102.proposed := by
  dsimp only [StepValid,centerStep102]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-235829481014,-235829453993⟩,⟨8677149893073,8677149961194⟩,⟨3916167671857,3916167702599⟩,⟨-52473617494539,-52473617489730⟩,⟨-33535333644379,-33535333564923⟩,⟨-10688317881777,-10688317880844⟩⟩⟩
noncomputable def centerBoxes104 := centerStep103.proposed :: centerBoxes103
theorem centerAccepted103 : StepValid centerStep103.shape centerBoxes103 centerStep103.proposed := by
  dsimp only [StepValid,centerStep103]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-11185716220,-11185714937⟩,⟨439712067307,439712073772⟩,⟨92016205293,92016217496⟩,⟨-4559887406254,-4559887389702⟩,⟨1626691102345,1626691163916⟩,⟨2606085749954,2606085774448⟩⟩⟩
noncomputable def centerBoxes105 := centerStep104.proposed :: centerBoxes104
theorem centerAccepted104 : StepValid centerStep104.shape centerBoxes104 centerStep104.proposed := by
  dsimp only [StepValid,centerStep104]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨438733046941,438733210351⟩,⟨838205197818,838208520063⟩,⟨-80865949714,-80863039167⟩,⟨-18375327135259,-18375232210647⟩,⟨-5426364661895,-5426263264407⟩,⟨-1254633963258,-1254524855514⟩⟩⟩
noncomputable def centerBoxes106 := centerStep105.proposed :: centerBoxes105
theorem centerAccepted105 : StepValid centerStep105.shape centerBoxes105 centerStep105.proposed := by
  dsimp only [StepValid,centerStep105]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-101182341120,-101182341120⟩,⟨-874025844736,-874025844736⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes107 := centerStep106.proposed :: centerBoxes106
theorem centerAccepted106 : StepValid centerStep106.shape centerBoxes106 centerStep106.proposed := by
  dsimp only [StepValid,centerStep106]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4799217422,4799217424⟩,⟨29381556837,29381556840⟩,⟨40216028160,40216028160⟩,⟨-312908080744,-312908080740⟩,⟨246208790528,246208790528⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes108 := centerStep107.proposed :: centerBoxes107
theorem centerAccepted107 : StepValid centerStep107.shape centerBoxes107 centerStep107.proposed := by
  dsimp only [StepValid,centerStep107]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨10411066024,10411066282⟩,⟨11586821578,11586823154⟩,⟨87241666214,87241668331⟩,⟨-866866999464,-866866982681⟩,⟨97094151476,97094164437⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes109 := centerStep108.proposed :: centerBoxes108
theorem centerAccepted108 : StepValid centerStep108.shape centerBoxes108 centerStep108.proposed := by
  dsimp only [StepValid,centerStep108]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1459624049322,1459624070222⟩,⟨-7163859041440,-7163858673962⟩,⟨-1336085741025,-1336085675577⟩,⟨103165362265918,103165369414373⟩,⟨21797048957155,21797050401731⟩,⟨4847223494707,4847223768160⟩⟩⟩
noncomputable def centerBoxes110 := centerStep109.proposed :: centerBoxes109
theorem centerAccepted109 : StepValid centerStep109.shape centerBoxes109 centerStep109.proposed := by
  dsimp only [StepValid,centerStep109]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨13820901902,13820902443⟩,⟨-52451476118,-52451468643⟩,⟨103163944822,103163950227⟩,⟨-324918142530,-324917983592⟩,⟨-247215693254,-247215609849⟩,⟨-166128242495,-166128223235⟩⟩⟩
noncomputable def centerBoxes111 := centerStep110.proposed :: centerBoxes110
theorem centerAccepted110 : StepValid centerStep110.shape centerBoxes110 centerStep110.proposed := by
  dsimp only [StepValid,centerStep110]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-13820902443,-13820901902⟩,⟨52451468643,52451476118⟩,⟨-103163950227,-103163944822⟩,⟨324917983592,324918142530⟩,⟨247215609849,247215693254⟩,⟨166128223235,166128242495⟩⟩⟩
noncomputable def centerBoxes112 := centerStep111.proposed :: centerBoxes111
theorem centerAccepted111 : StepValid centerStep111.shape centerBoxes111 centerStep111.proposed := by
  dsimp only [StepValid,centerStep111]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-115003243563,-115003243022⟩,⟨-821574376093,-821574368618⟩,⟨-103163950227,-103163944822⟩,⟨2523941239144,2523941398082⟩,⟨247215609849,247215693254⟩,⟨166128223235,166128242495⟩⟩⟩
noncomputable def centerBoxes113 := centerStep112.proposed :: centerBoxes112
theorem centerAccepted112 : StepValid centerStep112.shape centerBoxes112 centerStep112.proposed := by
  dsimp only [StepValid,centerStep112]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨90473874579,90473876412⟩,⟨-587906257078,-587906252454⟩,⟨595544507296,595544522644⟩,⟨3555265057222,3555265057590⟩,⟨-3321920494386,-3321920455552⟩,⟨-2370175562841,-2370175562714⟩⟩⟩
noncomputable def centerBoxes114 := centerStep113.proposed :: centerBoxes113
theorem centerAccepted113 : StepValid centerStep113.shape centerBoxes113 centerStep113.proposed := by
  dsimp only [StepValid,centerStep113]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨120105908691,120105912845⟩,⟨-1369939328847,-1369939269350⟩,⟨680656948207,680656987517⟩,⟨20869697471440,20869698752948⟩,⟨-5782199450611,-5782198841049⟩,⟨-4194967278964,-4194967094957⟩⟩⟩
noncomputable def centerBoxes115 := centerStep114.proposed :: centerBoxes114
theorem centerAccepted114 : StepValid centerStep114.shape centerBoxes114 centerStep114.proposed := by
  dsimp only [StepValid,centerStep114]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-120105912845,-120105908691⟩,⟨1369939269350,1369939328847⟩,⟨-680656987517,-680656948207⟩,⟨-20869698752948,-20869697471440⟩,⟨5782198841049,5782199450611⟩,⟨4194967094957,4194967278964⟩⟩⟩
noncomputable def centerBoxes116 := centerStep115.proposed :: centerBoxes115
theorem centerAccepted115 : StepValid centerStep115.shape centerBoxes115 centerStep115.proposed := by
  dsimp only [StepValid,centerStep115]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨979405714931,979405719085⟩,⟨1369939269350,1369939328847⟩,⟨-680656987517,-680656948207⟩,⟨-20869698752948,-20869697471440⟩,⟨5782198841049,5782199450611⟩,⟨4194967094957,4194967278964⟩⟩⟩
noncomputable def centerBoxes117 := centerStep116.proposed :: centerBoxes116
theorem centerAccepted116 : StepValid centerStep116.shape centerBoxes116 centerStep116.proposed := by
  dsimp only [StepValid,centerStep116]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨124853959257,124853959789⟩,⟨778459095492,778459105646⟩,⟨185746197260,185746203432⟩,⟨-2490467016846,-2490466773619⟩,⟨-672629349930,-672629225595⟩,⟨-153452517659,-153452471000⟩⟩⟩
noncomputable def centerBoxes118 := centerStep117.proposed :: centerBoxes117
theorem centerAccepted117 : StepValid centerStep117.shape centerBoxes117 centerStep117.proposed := by
  dsimp only [StepValid,centerStep117]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨12028745828,12028745942⟩,⟨171864879620,171864881994⟩,⟨21580832648,21580833882⟩,⟨699807052710,699807110787⟩,⟨102456845062,102456872240⟩,⟨-15393174587,-15393168364⟩⟩⟩
noncomputable def centerBoxes119 := centerStep118.proposed :: centerBoxes118
theorem centerAccepted118 : StepValid centerStep118.shape centerBoxes118 centerStep118.proposed := by
  dsimp only [StepValid,centerStep118]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨174014134273,174014289777⟩,⟨1677089107659,1677094588740⟩,⟨107800361375,107803038195⟩,⟨-2024779308769,-2024569716871⟩,⟨469844748398,469977344275⟩,⟨-533873158426,-533775212367⟩⟩⟩
noncomputable def centerBoxes120 := centerStep119.proposed :: centerBoxes119
theorem centerAccepted119 : StepValid centerStep119.shape centerBoxes119 centerStep119.proposed := by
  dsimp only [StepValid,centerStep119]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-174014289777,-174014134273⟩,⟨-1677094588740,-1677089107659⟩,⟨-107803038195,-107800361375⟩,⟨2024569716871,2024779308769⟩,⟨-469977344275,-469844748398⟩,⟨533775212367,533873158426⟩⟩⟩
noncomputable def centerBoxes121 := centerStep120.proposed :: centerBoxes120
theorem centerAccepted120 : StepValid centerStep120.shape centerBoxes120 centerStep120.proposed := by
  dsimp only [StepValid,centerStep120]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨57881248060,57881464145⟩,⟨-85224406432,-85217269713⟩,⟨131605067401,131608605172⟩,⟨-1814596975792,-1814333545926⟩,⟨-1753325588372,-1753154039057⟩,⟨404545106414,404675524992⟩⟩⟩
noncomputable def centerBoxes122 := centerStep121.proposed :: centerBoxes121
theorem centerAccepted121 : StepValid centerStep121.shape centerBoxes121 centerStep121.proposed := by
  dsimp only [StepValid,centerStep121]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨27594445070640,27594470026444⟩,⟨-238203453641420,-238202839972263⟩,⟨-82005653861545,-82005231788456⟩,⟨3293726814428611,3293748343465347⟩,⟨1257093206861094,1257110382267573⟩,⟨291705598823592,291721177341379⟩⟩⟩
noncomputable def centerBoxes123 := centerStep122.proposed :: centerBoxes122
theorem centerAccepted122 : StepValid centerStep122.shape centerBoxes122 centerStep122.proposed := by
  dsimp only [StepValid,centerStep122]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨14177668292,14177668414⟩,⟨176794310740,176794313800⟩,⟨42184452730,42184454314⟩,⟨536699907709,536699994118⟩,⟨110258731912,110258772974⟩,⟨27907836422,27907851342⟩⟩⟩
noncomputable def centerBoxes124 := centerStep123.proposed :: centerBoxes123
theorem centerAccepted123 : StepValid centerStep123.shape centerBoxes123 centerStep123.proposed := by
  dsimp only [StepValid,centerStep123]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨355816963668,355817288524⟩,⟨1365489257039,1365501285966⟩,⟨1280200349,1286649099⟩,⟨-20662564493726,-20662073497731⟩,⟨-3348247436807,-3347930313342⟩,⟨-1830741020420,-1830506479506⟩⟩⟩
noncomputable def centerBoxes125 := centerStep124.proposed :: centerBoxes124
theorem centerAccepted124 : StepValid centerStep124.shape centerBoxes124 centerStep124.proposed := by
  dsimp only [StepValid,centerStep124]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-355817288524,-355816963668⟩,⟨-1365501285966,-1365489257039⟩,⟨-1286649099,-1280200349⟩,⟨20662073497731,20662564493726⟩,⟨3347930313342,3348247436807⟩,⟨1830506479506,1830741020420⟩⟩⟩
noncomputable def centerBoxes126 := centerStep125.proposed :: centerBoxes125
theorem centerAccepted125 : StepValid centerStep125.shape centerBoxes125 centerStep125.proposed := by
  dsimp only [StepValid,centerStep125]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨82915758417,82916246683⟩,⟨-527296088148,-527280736976⟩,⟨-82152598813,-82143239516⟩,⟨2286746362472,2287332283079⟩,⟨-2078434348553,-2078015827600⟩,⟨575872516248,576216164906⟩⟩⟩
noncomputable def centerBoxes127 := centerStep126.proposed :: centerBoxes126
theorem centerAccepted126 : StepValid centerStep126.shape centerBoxes126 centerStep126.proposed := by
  dsimp only [StepValid,centerStep126]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨241347318600,241347318602⟩,⟨1551893362031,1551893362035⟩,⟨305934885272,305934885274⟩,⟨-3904517942808,-3904517942803⟩,⟨-1539446302312,-1539446302308⟩,⟨-347391131648,-347391131648⟩⟩⟩
noncomputable def centerBoxes128 := centerStep127.proposed :: centerBoxes127
theorem centerAccepted127 : StepValid centerStep127.shape centerBoxes127 centerStep127.proposed := by
  dsimp only [StepValid,centerStep127]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1663698597265,-1663697118487⟩,⟨-4148864372479,-4148822735017⟩,⟨461752422806,461776593724⟩,⟨42121927309373,42123426875523⟩,⟨-7646643725985,-7645579197139⟩,⟨1871532870653,1872427886465⟩⟩⟩
noncomputable def centerBoxes129 := centerStep128.proposed :: centerBoxes128
theorem centerAccepted128 : StepValid centerStep128.shape centerBoxes128 centerStep128.proposed := by
  dsimp only [StepValid,centerStep128]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-188919655342,-188919486615⟩,⟨-1649026187464,-1649020395008⟩,⟨-228623393846,-228620389758⟩,⟨2676669549486,2676902604834⟩,⟨-224502288072,-224356135361⟩,⟨600725102986,600835185340⟩⟩⟩
noncomputable def centerBoxes130 := centerStep129.proposed :: centerBoxes129
theorem centerAccepted129 : StepValid centerStep129.shape centerBoxes129 centerStep129.proposed := by
  dsimp only [StepValid,centerStep129]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨52427663258,52427831987⟩,⟨-97132825433,-97127032973⟩,⟨77311491426,77314495516⟩,⟨-1227848393322,-1227615337969⟩,⟨-1763948590384,-1763802437669⟩,⟨253333971338,253444053692⟩⟩⟩
noncomputable def centerBoxes131 := centerStep130.proposed :: centerBoxes130
theorem centerAccepted130 : StepValid centerStep130.shape centerBoxes130 centerStep130.proposed := by
  dsimp only [StepValid,centerStep130]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨4364908437,4364950437⟩,⟨-34185320626,-34183832833⟩,⟨5599778225,5600612303⟩,⟨65271717662,65332907801⟩,⟨-298385821501,-298344872878⟩,⟨41155914362,41186902128⟩⟩⟩
noncomputable def centerBoxes132 := centerStep131.proposed :: centerBoxes131
theorem centerAccepted131 : StepValid centerStep131.shape centerBoxes131 centerStep131.proposed := by
  dsimp only [StepValid,centerStep131]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨2499891593,2499907684⟩,⟨-9263137058,-9262554844⟩,⟨7372838514,7373148732⟩,⟨-99934857166,-99910208103⟩,⟨-181880342512,-181864517856⟩,⟨35031507371,35042928143⟩⟩⟩
noncomputable def centerBoxes133 := centerStep132.proposed :: centerBoxes132
theorem centerAccepted132 : StepValid centerStep132.shape centerBoxes132 centerStep132.proposed := by
  dsimp only [StepValid,centerStep132]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨4336894296,4336922300⟩,⟨-33340084082,-33338962549⟩,⟨4996314058,4996902665⟩,⟨38127820028,38179167368⟩,⟨-280283683447,-280251896735⟩,⟨31809511260,31831369555⟩⟩⟩
noncomputable def centerBoxes134 := centerStep133.proposed :: centerBoxes133
theorem centerAccepted133 : StepValid centerStep133.shape centerBoxes133 centerStep133.proposed := by
  dsimp only [StepValid,centerStep133]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-4336922300,-4336894296⟩,⟨33338962549,33340084082⟩,⟨-4996902665,-4996314058⟩,⟨-38179167368,-38127820028⟩,⟨280251896735,280283683447⟩,⟨-31831369555,-31809511260⟩⟩⟩
noncomputable def centerBoxes135 := centerStep134.proposed :: centerBoxes134
theorem centerAccepted134 : StepValid centerStep134.shape centerBoxes134 centerStep134.proposed := by
  dsimp only [StepValid,centerStep134]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨27986137,28056141⟩,⟨-846358077,-843748751⟩,⟨602875560,604298245⟩,⟨27092550294,27205087773⟩,⟨-18133924766,-18061189431⟩,⟨9324544807,9377390868⟩⟩⟩
noncomputable def centerBoxes136 := centerStep135.proposed :: centerBoxes135
theorem centerAccepted135 : StepValid centerStep135.shape centerBoxes135 centerStep135.proposed := by
  dsimp only [StepValid,centerStep135]
  exact ⟨by decide,by decide⟩
noncomputable def centerProgram : List (Instruction 40) := [centerStep0,centerStep1,centerStep2,centerStep3,centerStep4,centerStep5,centerStep6,centerStep7,centerStep8,centerStep9,centerStep10,centerStep11,centerStep12,centerStep13,centerStep14,centerStep15,centerStep16,centerStep17,centerStep18,centerStep19,centerStep20,centerStep21,centerStep22,centerStep23,centerStep24,centerStep25,centerStep26,centerStep27,centerStep28,centerStep29,centerStep30,centerStep31,centerStep32,centerStep33,centerStep34,centerStep35,centerStep36,centerStep37,centerStep38,centerStep39,centerStep40,centerStep41,centerStep42,centerStep43,centerStep44,centerStep45,centerStep46,centerStep47,centerStep48,centerStep49,centerStep50,centerStep51,centerStep52,centerStep53,centerStep54,centerStep55,centerStep56,centerStep57,centerStep58,centerStep59,centerStep60,centerStep61,centerStep62,centerStep63,centerStep64,centerStep65,centerStep66,centerStep67,centerStep68,centerStep69,centerStep70,centerStep71,centerStep72,centerStep73,centerStep74,centerStep75,centerStep76,centerStep77,centerStep78,centerStep79,centerStep80,centerStep81,centerStep82,centerStep83,centerStep84,centerStep85,centerStep86,centerStep87,centerStep88,centerStep89,centerStep90,centerStep91,centerStep92,centerStep93,centerStep94,centerStep95,centerStep96,centerStep97,centerStep98,centerStep99,centerStep100,centerStep101,centerStep102,centerStep103,centerStep104,centerStep105,centerStep106,centerStep107,centerStep108,centerStep109,centerStep110,centerStep111,centerStep112,centerStep113,centerStep114,centerStep115,centerStep116,centerStep117,centerStep118,centerStep119,centerStep120,centerStep121,centerStep122,centerStep123,centerStep124,centerStep125,centerStep126,centerStep127,centerStep128,centerStep129,centerStep130,centerStep131,centerStep132,centerStep133,centerStep134,centerStep135]
theorem centerAccepted : Accepted centerProgram centerInitial :=
  ⟨centerAccepted0,⟨centerAccepted1,⟨centerAccepted2,⟨centerAccepted3,⟨centerAccepted4,⟨centerAccepted5,⟨centerAccepted6,⟨centerAccepted7,⟨centerAccepted8,⟨centerAccepted9,⟨centerAccepted10,⟨centerAccepted11,⟨centerAccepted12,⟨centerAccepted13,⟨centerAccepted14,⟨centerAccepted15,⟨centerAccepted16,⟨centerAccepted17,⟨centerAccepted18,⟨centerAccepted19,⟨centerAccepted20,⟨centerAccepted21,⟨centerAccepted22,⟨centerAccepted23,⟨centerAccepted24,⟨centerAccepted25,⟨centerAccepted26,⟨centerAccepted27,⟨centerAccepted28,⟨centerAccepted29,⟨centerAccepted30,⟨centerAccepted31,⟨centerAccepted32,⟨centerAccepted33,⟨centerAccepted34,⟨centerAccepted35,⟨centerAccepted36,⟨centerAccepted37,⟨centerAccepted38,⟨centerAccepted39,⟨centerAccepted40,⟨centerAccepted41,⟨centerAccepted42,⟨centerAccepted43,⟨centerAccepted44,⟨centerAccepted45,⟨centerAccepted46,⟨centerAccepted47,⟨centerAccepted48,⟨centerAccepted49,⟨centerAccepted50,⟨centerAccepted51,⟨centerAccepted52,⟨centerAccepted53,⟨centerAccepted54,⟨centerAccepted55,⟨centerAccepted56,⟨centerAccepted57,⟨centerAccepted58,⟨centerAccepted59,⟨centerAccepted60,⟨centerAccepted61,⟨centerAccepted62,⟨centerAccepted63,⟨centerAccepted64,⟨centerAccepted65,⟨centerAccepted66,⟨centerAccepted67,⟨centerAccepted68,⟨centerAccepted69,⟨centerAccepted70,⟨centerAccepted71,⟨centerAccepted72,⟨centerAccepted73,⟨centerAccepted74,⟨centerAccepted75,⟨centerAccepted76,⟨centerAccepted77,⟨centerAccepted78,⟨centerAccepted79,⟨centerAccepted80,⟨centerAccepted81,⟨centerAccepted82,⟨centerAccepted83,⟨centerAccepted84,⟨centerAccepted85,⟨centerAccepted86,⟨centerAccepted87,⟨centerAccepted88,⟨centerAccepted89,⟨centerAccepted90,⟨centerAccepted91,⟨centerAccepted92,⟨centerAccepted93,⟨centerAccepted94,⟨centerAccepted95,⟨centerAccepted96,⟨centerAccepted97,⟨centerAccepted98,⟨centerAccepted99,⟨centerAccepted100,⟨centerAccepted101,⟨centerAccepted102,⟨centerAccepted103,⟨centerAccepted104,⟨centerAccepted105,⟨centerAccepted106,⟨centerAccepted107,⟨centerAccepted108,⟨centerAccepted109,⟨centerAccepted110,⟨centerAccepted111,⟨centerAccepted112,⟨centerAccepted113,⟨centerAccepted114,⟨centerAccepted115,⟨centerAccepted116,⟨centerAccepted117,⟨centerAccepted118,⟨centerAccepted119,⟨centerAccepted120,⟨centerAccepted121,⟨centerAccepted122,⟨centerAccepted123,⟨centerAccepted124,⟨centerAccepted125,⟨centerAccepted126,⟨centerAccepted127,⟨centerAccepted128,⟨centerAccepted129,⟨centerAccepted130,⟨centerAccepted131,⟨centerAccepted132,⟨centerAccepted133,⟨centerAccepted134,⟨centerAccepted135,True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
noncomputable def center_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨57881248060,57881464145⟩,⟨-85224406432,-85217269713⟩,⟨131605067401,131608605172⟩,⟨-1814596975792,-1814333545926⟩,⟨-1753325588372,-1753154039057⟩,⟨404545106414,404675524992⟩⟩
theorem center_m11_eq : (finalBoxes centerProgram centerInitial).getD 14 (zeroBox 40)=center_m11 := rfl
noncomputable def center_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨27986137,28056141⟩,⟨-846358077,-843748751⟩,⟨602875560,604298245⟩,⟨27092550294,27205087773⟩,⟨-18133924766,-18061189431⟩,⟨9324544807,9377390868⟩⟩
theorem center_kdet_eq : (finalBoxes centerProgram centerInitial).getD 0 (zeroBox 40)=center_kdet := rfl
noncomputable def wholeInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨112528143155,112957639885⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨129278515609,133143986176⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
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
noncomputable def wholeStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-112957639885,-112528143155⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes3 := wholeStep2.proposed :: wholeBoxes2
theorem wholeAccepted2 : StepValid wholeStep2.shape wholeBoxes2 wholeStep2.proposed := by
  dsimp only [StepValid,wholeStep2]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨436798174003,437227670733⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes4 := wholeStep3.proposed :: wholeBoxes3
theorem wholeAccepted3 : StepValid wholeStep3.shape wholeBoxes3 wholeStep3.proposed := by
  dsimp only [StepValid,wholeStep3]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨51357910302,52945538253⟩,⟨-133143986176,-129278515609⟩,⟨436798174003,437227670733⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes5 := wholeStep4.proposed :: wholeBoxes4
theorem wholeAccepted4 : StepValid wholeStep4.shape wholeBoxes4 wholeStep4.proposed := by
  dsimp only [StepValid,wholeStep4]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨163886053457,165903178138⟩,⟨966367641600,970233112167⟩,⟨436798174003,437227670733⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes6 := wholeStep5.proposed :: wholeBoxes5
theorem wholeAccepted5 : StepValid wholeStep5.shape wholeBoxes5 wholeStep5.proposed := by
  dsimp only [StepValid,wholeStep5]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨50928413572,53375034983⟩,⟨-133143986176,-129278515609⟩,⟨436798174003,437227670733⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes7 := wholeStep6.proposed :: wholeBoxes6
theorem wholeAccepted6 : StepValid wholeStep6.shape wholeBoxes6 wholeStep6.proposed := by
  dsimp only [StepValid,wholeStep6]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep7 : Instruction 40 := ⟨.log 7,⟨⟨-2506246686976,-2502058008320⟩,⟨10702470597344,10743319721800⟩,⟨0,0⟩,⟨-104972894991822,-104176139654566⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes8 := wholeStep7.proposed :: wholeBoxes7
theorem wholeAccepted7 : StepValid wholeStep7.shape wholeBoxes7 wholeStep7.proposed := by
  dsimp only [StepValid,wholeStep7]
  exact ⟨by decide,by decide,lc19,by decide⟩
noncomputable def wholeStep8 : Instruction 40 := ⟨.mul 8 0,⟨⟨-257477686983,-256069999288⟩,⟨-1410915711782,-1398349771273⟩,⟨0,0⟩,⟨10620616435743,10824862650847⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes9 := wholeStep8.proposed :: wholeBoxes8
theorem wholeAccepted8 : StepValid wholeStep8.shape wholeBoxes8 wholeStep8.proposed := by
  dsimp only [StepValid,wholeStep8]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep9 : Instruction 40 := ⟨.neg 0,⟨⟨256069999288,257477686983⟩,⟨1398349771273,1410915711782⟩,⟨0,0⟩,⟨-10824862650847,-10620616435743⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes10 := wholeStep9.proposed :: wholeBoxes9
theorem wholeAccepted9 : StepValid wholeStep9.shape wholeBoxes9 wholeStep9.proposed := by
  dsimp only [StepValid,wholeStep9]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep10 : Instruction 40 := ⟨.add 12 7,⟨⟨986553987891,986983484621⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes11 := wholeStep10.proposed :: wholeBoxes10
theorem wholeAccepted10 : StepValid wholeStep10.shape wholeBoxes10 wholeStep10.proposed := by
  dsimp only [StepValid,wholeStep10]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep11 : Instruction 40 := ⟨.log 0,⟨⟨-119190727104,-118712158336⟩,⟨-1225402597783,-1224869350350⟩,⟨0,0⟩,⟨-1365707727613,-1364519380719⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes12 := wholeStep11.proposed :: wholeBoxes11
theorem wholeAccepted11 : StepValid wholeStep11.shape wholeBoxes11 wholeStep11.proposed := by
  dsimp only [StepValid,wholeStep11]
  exact ⟨by decide,by decide,lc20,by decide⟩
noncomputable def wholeStep12 : Instruction 40 := ⟨.mul 1 0,⟨⟨-106992301127,-106516338944⟩,⟨-981278142331,-979842436080⟩,⟨0,0⟩,⟨1223802623334,1226468860601⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes13 := wholeStep12.proposed :: wholeBoxes12
theorem wholeAccepted12 : StepValid wholeStep12.shape wholeBoxes12 wholeStep12.proposed := by
  dsimp only [StepValid,wholeStep12]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep13 : Instruction 40 := ⟨.neg 0,⟨⟨106516338944,106992301127⟩,⟨979842436080,981278142331⟩,⟨0,0⟩,⟨-1226468860601,-1223802623334⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes14 := wholeStep13.proposed :: wholeBoxes13
theorem wholeAccepted13 : StepValid wholeStep13.shape wholeBoxes13 wholeStep13.proposed := by
  dsimp only [StepValid,wholeStep13]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep14 : Instruction 40 := ⟨.add 4 0,⟨⟨362586338232,364469988110⟩,⟨2378192207353,2392193854113⟩,⟨0,0⟩,⟨-12051331511448,-11844419059077⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes15 := wholeStep14.proposed :: wholeBoxes14
theorem wholeAccepted14 : StepValid wholeStep14.shape wholeBoxes14 wholeStep14.proposed := by
  dsimp only [StepValid,wholeStep14]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2092865438912,-2079415114368⟩,⟨6404533478929,6509294512733⟩,⟨2894849132474,2933360696751⟩,⟨-38536122750417,-37305698317804⟩,⟨-24742614835106,-24149111508999⟩,⟨-7825842637652,-7621703389113⟩⟩⟩
noncomputable def wholeBoxes16 := wholeStep15.proposed :: wholeBoxes15
theorem wholeAccepted15 : StepValid wholeStep15.shape wholeBoxes15 wholeStep15.proposed := by
  dsimp only [StepValid,wholeStep15]
  exact ⟨by decide,by decide,lc21,by decide⟩
noncomputable def wholeStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-315788409108,-309944095163⟩,⟨-892172131033,-845436109448⟩,⟨-400753634803,-383471035760⟩,⟨5443328145475,5927342933719⟩,⟨3434651915544,3670279203641⟩,⟨1119221874398,1196896883502⟩⟩⟩
noncomputable def wholeBoxes17 := wholeStep16.proposed :: wholeBoxes16
theorem wholeAccepted16 : StepValid wholeStep16.shape wholeBoxes16 wholeStep16.proposed := by
  dsimp only [StepValid,wholeStep16]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep17 : Instruction 40 := ⟨.neg 0,⟨⟨309944095163,315788409108⟩,⟨845436109448,892172131033⟩,⟨383471035760,400753634803⟩,⟨-5927342933719,-5443328145475⟩,⟨-3670279203641,-3434651915544⟩,⟨-1196896883502,-1119221874398⟩⟩⟩
noncomputable def wholeBoxes18 := wholeStep17.proposed :: wholeBoxes17
theorem wholeAccepted17 : StepValid wholeStep17.shape wholeBoxes17 wholeStep17.proposed := by
  dsimp only [StepValid,wholeStep17]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-165903178138,-163886053457⟩,⟨-970233112167,-966367641600⟩,⟨-437227670733,-436798174003⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes19 := wholeStep18.proposed :: wholeBoxes18
theorem wholeAccepted18 : StepValid wholeStep18.shape wholeBoxes18 wholeStep18.proposed := by
  dsimp only [StepValid,wholeStep18]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨933608449638,935625574319⟩,⟨-970233112167,-966367641600⟩,⟨-437227670733,-436798174003⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes20 := wholeStep19.proposed :: wholeBoxes19
theorem wholeAccepted19 : StepValid wholeStep19.shape wholeBoxes19 wholeStep19.proposed := by
  dsimp only [StepValid,wholeStep19]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep20 : Instruction 40 := ⟨.log 0,⟨⟨-179840799104,-177467791872⟩,⟨-1142644530365,-1135638537263⟩,⟨-514923475835,-513308618842⟩,⟨-1187469499905,-1172952477022⟩,⟨756980807044,764721451051⟩,⟨-241149051332,-239638882865⟩⟩⟩
noncomputable def wholeBoxes21 := wholeStep20.proposed :: wholeBoxes20
theorem wholeAccepted20 : StepValid wholeStep20.shape wholeBoxes20 wholeStep20.proposed := by
  dsimp only [StepValid,wholeStep20]
  exact ⟨by decide,by decide,lc22,by decide⟩
noncomputable def wholeStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-153034899038,-150690020773⟩,⟨-816351815478,-805588784636⟩,⟨-367670477658,-364341658612⟩,⟨985766598291,1020621106384⟩,⟨1365220947912,1382028730488⟩,⟨202634796706,206044840513⟩⟩⟩
noncomputable def wholeBoxes22 := wholeStep21.proposed :: wholeBoxes21
theorem wholeAccepted21 : StepValid wholeStep21.shape wholeBoxes21 wholeStep21.proposed := by
  dsimp only [StepValid,wholeStep21]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep22 : Instruction 40 := ⟨.neg 0,⟨⟨150690020773,153034899038⟩,⟨805588784636,816351815478⟩,⟨364341658612,367670477658⟩,⟨-1020621106384,-985766598291⟩,⟨-1382028730488,-1365220947912⟩,⟨-206044840513,-202634796706⟩⟩⟩
noncomputable def wholeBoxes23 := wholeStep22.proposed :: wholeBoxes22
theorem wholeAccepted22 : StepValid wholeStep22.shape wholeBoxes22 wholeStep22.proposed := by
  dsimp only [StepValid,wholeStep22]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨460634115936,468823308146⟩,⟨1651024894084,1708523946511⟩,⟨747812694372,768424112461⟩,⟨-6947964040103,-6429094743766⟩,⟨-5052307934129,-4799872863456⟩,⟨-1402941724015,-1321856671104⟩⟩⟩
noncomputable def wholeBoxes24 := wholeStep23.proposed :: wholeBoxes23
theorem wholeAccepted23 : StepValid wholeStep23.shape wholeBoxes23 wholeStep23.proposed := by
  dsimp only [StepValid,wholeStep23]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨823220454168,833293296256⟩,⟨4029217101437,4100717800624⟩,⟨747812694372,768424112461⟩,⟨-18999295551551,-18273513802843⟩,⟨-5052307934129,-4799872863456⟩,⟨-1402941724015,-1321856671104⟩⟩⟩
noncomputable def wholeBoxes25 := wholeStep24.proposed :: wholeBoxes24
theorem wholeAccepted24 : StepValid wholeStep24.shape wholeBoxes24 wholeStep24.proposed := by
  dsimp only [StepValid,wholeStep24]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨101856827144,106750069966⟩,⟨-266287972352,-258557031218⟩,⟨873596348006,874455341466⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes26 := wholeStep25.proposed :: wholeBoxes25
theorem wholeAccepted25 : StepValid wholeStep25.shape wholeBoxes25 wholeStep25.proposed := by
  dsimp only [StepValid,wholeStep25]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep26 : Instruction 40 := ⟨.inv 0,⟨⟨11324824611353,11868873727095⟩,⟨27429612285111,31029224132635⟩,⟨-101895968280763,-92677460777658⟩,⟨132873339046202,162241636807594⟩,⟨-299492204027076,-192702804132770⟩,⟨1516864416175406,1749582747379255⟩⟩⟩
noncomputable def wholeBoxes27 := wholeStep26.proposed :: wholeBoxes26
theorem wholeAccepted26 : StepValid wholeStep26.shape wholeBoxes26 wholeStep26.proposed := by
  dsimp only [StepValid,wholeStep26]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨8479061998451,8995132621656⟩,⟨62037356545114,67782226527750⟩,⟨-69522120318623,-61094081131946⟩,⟨95427400557334,166196253263053⟩,⟨-642889471664159,-511653173945596⟩,⟨978128662106781,1186285786726601⟩⟩⟩
noncomputable def wholeBoxes28 := wholeStep27.proposed :: wholeBoxes27
theorem wholeAccepted27 : StepValid wholeStep27.shape wholeBoxes27 wholeStep27.proposed := by
  dsimp only [StepValid,wholeStep27]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep28 : Instruction 40 := ⟨.contact 0,⟨⟨92679355392,98257377536⟩,⟨-776949851813,-632250994778⟩,⟨622637644830,796893283775⟩,⟨6661850229613,11261744661403⟩,⟨-7333838454041,-1067522953414⟩,⟨-5289404130890,2901875552623⟩⟩⟩
noncomputable def wholeBoxes29 := wholeStep28.proposed :: wholeBoxes28
theorem wholeAccepted28 : StepValid wholeStep28.shape wholeBoxes28 wholeStep28.proposed := by
  dsimp only [StepValid,wholeStep28]
  exact ⟨by decide,by decide,(⟨⟨92679355392,98257377536⟩,⟨-12603088450,-11205624468⟩,⟨2691008175,3219190823⟩⟩ : DyadicJetEnclosure 40),brwhole28_jet,by decide⟩
noncomputable def wholeStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes30 := wholeStep29.proposed :: wholeBoxes29
theorem wholeAccepted29 : StepValid wholeStep29.shape wholeBoxes29 wholeStep29.proposed := by
  dsimp only [StepValid,wholeStep29]
  exact ⟨by decide,by decide,lc4,by decide⟩
noncomputable def wholeStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1192190983168,1197769005312⟩,⟨-776949851813,-632250994778⟩,⟨622637644830,796893283775⟩,⟨6661850229613,11261744661403⟩,⟨-7333838454041,-1067522953414⟩,⟨-5289404130890,2901875552623⟩⟩⟩
noncomputable def wholeBoxes31 := wholeStep30.proposed :: wholeBoxes30
theorem wholeAccepted30 : StepValid wholeStep30.shape wholeBoxes30 wholeStep30.proposed := by
  dsimp only [StepValid,wholeStep30]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep31 : Instruction 40 := ⟨.log 0,⟨⟨88979814784,94112211520⟩,⟨-716550794570,-580385130478⟩,⟨571560398829,734943850422⟩,⟨5648378716069,10079911006973⟩,⟨-6462013248246,-500987852945⟩,⟨-5369469535212,2379172670666⟩⟩⟩
noncomputable def wholeBoxes32 := wholeStep31.proposed :: wholeBoxes31
theorem wholeAccepted31 : StepValid wholeStep31.shape wholeBoxes31 wholeStep31.proposed := by
  dsimp only [StepValid,wholeStep31]
  exact ⟨by decide,by decide,lc32,by decide⟩
noncomputable def wholeStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨96480046403,102522508296⟩,⟨-847087723071,-680472563301⟩,⟨670126006419,868831515584⟩,⟨7331086204942,12957317033789⟩,⟨-8705894258910,-1286935418738⟩,⟨-5654721156513,3905501985837⟩⟩⟩
noncomputable def wholeBoxes33 := wholeStep32.proposed :: wholeBoxes32
theorem wholeAccepted32 : StepValid wholeStep32.shape wholeBoxes32 wholeStep32.proposed := by
  dsimp only [StepValid,wholeStep32]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-98257377536,-92679355392⟩,⟨632250994778,776949851813⟩,⟨-796893283775,-622637644830⟩,⟨-11261744661403,-6661850229613⟩,⟨1067522953414,7333838454041⟩,⟨-2901875552623,5289404130890⟩⟩⟩
noncomputable def wholeBoxes34 := wholeStep33.proposed :: wholeBoxes33
theorem wholeAccepted33 : StepValid wholeStep33.shape wholeBoxes33 wholeStep33.proposed := by
  dsimp only [StepValid,wholeStep33]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1001254250240,1006832272384⟩,⟨632250994778,776949851813⟩,⟨-796893283775,-622637644830⟩,⟨-11261744661403,-6661850229613⟩,⟨1067522953414,7333838454041⟩,⟨-2901875552623,5289404130890⟩⟩⟩
noncomputable def wholeBoxes35 := wholeStep34.proposed :: wholeBoxes34
theorem wholeAccepted34 : StepValid wholeStep34.shape wholeBoxes34 wholeStep34.proposed := by
  dsimp only [StepValid,wholeStep34]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep35 : Instruction 40 := ⟨.log 0,⟨⟨-102928188608,-96819770432⟩,⟨690449978113,853195275888⟩,⟨-875095842437,-679951715056⟩,⟨-13028967561737,-7708651866200⟩,⟨1592771797672,8732593384207⟩,⟨-3883133490855,5387985435470⟩⟩⟩
noncomputable def wholeBoxes36 := wholeStep35.proposed :: wholeBoxes35
theorem wholeAccepted35 : StepValid wholeStep35.shape wholeBoxes35 wholeStep35.proposed := by
  dsimp only [StepValid,wholeStep35]
  exact ⟨by decide,by decide,lc33,by decide⟩
noncomputable def wholeStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-94252229273,-88167513833⟩,⟨556015888175,725604097389⟩,⟨-746505158314,-544588840461⟩,⟨-10550057446478,-4759740095096⟩,⟨-472846609905,7120524257569⟩,⟨-3280880113068,6473963742573⟩⟩⟩
noncomputable def wholeBoxes37 := wholeStep36.proposed :: wholeBoxes36
theorem wholeAccepted36 : StepValid wholeStep36.shape wholeBoxes36 wholeStep36.proposed := by
  dsimp only [StepValid,wholeStep36]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨2227817130,14354994463⟩,⟨-291071834896,45131534088⟩,⟨-76379151895,324242675123⟩,⟨-3218971241536,8197576938693⟩,⟨-9178740868815,5833588838831⟩,⟨-8935601269581,10379465728410⟩⟩⟩
noncomputable def wholeBoxes38 := wholeStep37.proposed :: wholeBoxes37
theorem wholeAccepted37 : StepValid wholeStep37.shape wholeBoxes37 wholeStep37.proposed := by
  dsimp only [StepValid,wholeStep37]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨1113908565,7177497232⟩,⟨-145535917448,22565767044⟩,⟨-38189575948,162121337562⟩,⟨-1609485620768,4098788469347⟩,⟨-4589370434408,2916794419416⟩,⟨-4467800634791,5189732864205⟩⟩⟩
noncomputable def wholeBoxes39 := wholeStep38.proposed :: wholeBoxes38
theorem wholeAccepted38 : StepValid wholeStep38.shape wholeBoxes38 wholeStep38.proposed := by
  dsimp only [StepValid,wholeStep38]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-7177497232,-1113908565⟩,⟨-22565767044,145535917448⟩,⟨-162121337562,38189575948⟩,⟨-4098788469347,1609485620768⟩,⟨-2916794419416,4589370434408⟩,⟨-5189732864205,4467800634791⟩⟩⟩
noncomputable def wholeBoxes40 := wholeStep39.proposed :: wholeBoxes39
theorem wholeAccepted39 : StepValid wholeStep39.shape wholeBoxes39 wholeStep39.proposed := by
  dsimp only [StepValid,wholeStep39]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨754945886384,761009494315⟩,⟨-22565767044,145535917448⟩,⟨-162121337562,38189575948⟩,⟨-4098788469347,1609485620768⟩,⟨-2916794419416,4589370434408⟩,⟨-5189732864205,4467800634791⟩⟩⟩
noncomputable def wholeBoxes41 := wholeStep40.proposed :: wholeBoxes40
theorem wholeAccepted40 : StepValid wholeStep40.shape wholeBoxes40 wholeStep40.proposed := by
  dsimp only [StepValid,wholeStep40]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨7812071013,8780727731⟩,⟨-138863569948,-106586621116⟩,⟨104965975998,142428042164⟩,⟨1850198360254,3110836713208⟩,⟨-2436990785114,-896035288892⟩,⟨-240189077651,1673778729061⟩⟩⟩
noncomputable def wholeBoxes42 := wholeStep41.proposed :: wholeBoxes41
theorem wholeAccepted41 : StepValid wholeStep41.shape wholeBoxes41 wholeStep41.proposed := by
  dsimp only [StepValid,wholeStep41]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-8780727731,-7812071013⟩,⟨106586621116,138863569948⟩,⟨-142428042164,-104965975998⟩,⟨-3110836713208,-1850198360254⟩,⟨896035288892,2436990785114⟩,⟨-1673778729061,240189077651⟩⟩⟩
noncomputable def wholeBoxes43 := wholeStep42.proposed :: wholeBoxes42
theorem wholeAccepted42 : StepValid wholeStep42.shape wholeBoxes42 wholeStep42.proposed := by
  dsimp only [StepValid,wholeStep42]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1090730900045,1091699556763⟩,⟨106586621116,138863569948⟩,⟨-142428042164,-104965975998⟩,⟨-3110836713208,-1850198360254⟩,⟨896035288892,2436990785114⟩,⟨-1673778729061,240189077651⟩⟩⟩
noncomputable def wholeBoxes44 := wholeStep43.proposed :: wholeBoxes43
theorem wholeAccepted43 : StepValid wholeStep43.shape wholeBoxes43 wholeStep43.proposed := by
  dsimp only [StepValid,wholeStep43]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep44 : Instruction 40 := ⟨.log 0,⟨⟨-8815977088,-7839955648⟩,⟨107349342185,139981465480⟩,⟨-143574632822,-105717099925⟩,⟨-3153701306315,-1873919066632⟩,⟨912768757059,2474888160751⟩,⟨-1706001204064,231958066996⟩⟩⟩
noncomputable def wholeBoxes45 := wholeStep44.proposed :: wholeBoxes44
theorem wholeAccepted44 : StepValid wholeStep44.shape wholeBoxes44 wholeStep44.proposed := by
  dsimp only [StepValid,wholeStep44]
  exact ⟨by decide,by decide,lc30,by decide⟩
noncomputable def wholeStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-4407988544,-3919977824⟩,⟨53674671092,69990732740⟩,⟨-71787316411,-52858549962⟩,⟨-1576850653158,-936959533316⟩,⟨456384378529,1237444080376⟩,⟨-853000602032,115979033498⟩⟩⟩
noncomputable def wholeBoxes46 := wholeStep45.proposed :: wholeBoxes45
theorem wholeAccepted45 : StepValid wholeStep45.shape wholeBoxes45 wholeStep45.proposed := by
  dsimp only [StepValid,wholeStep45]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3919977824,4407988544⟩,⟨-69990732740,-53674671092⟩,⟨52858549962,71787316411⟩,⟨936959533316,1576850653158⟩,⟨-1237444080376,-456384378529⟩,⟨-115979033498,853000602032⟩⟩⟩
noncomputable def wholeBoxes47 := wholeStep46.proposed :: wholeBoxes46
theorem wholeAccepted46 : StepValid wholeStep46.shape wholeBoxes46 wholeStep46.proposed := by
  dsimp only [StepValid,wholeStep46]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨766043361440,766531391424⟩,⟨-69990732740,-53674671092⟩,⟨52858549962,71787316411⟩,⟨936959533316,1576850653158⟩,⟨-1237444080376,-456384378529⟩,⟨-115979033498,853000602032⟩⟩⟩
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
noncomputable def wholeStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272682725011,272924889191⟩,⟨26646655279,34715892487⟩,⟨-35607010541,-26241493999⟩,⟨-777709178302,-462549590063⟩,⟨224008822223,609247696279⟩,⟨-418444682266,60047269413⟩⟩⟩
noncomputable def wholeBoxes51 := wholeStep50.proposed :: wholeBoxes50
theorem wholeAccepted50 : StepValid wholeStep50.shape wholeBoxes50 wholeStep50.proposed := by
  dsimp only [StepValid,wholeStep50]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1532086722880,1533062782848⟩,⟨-139981465480,-107349342184⟩,⟨105717099924,143574632822⟩,⟨1873919066632,3153701306316⟩,⟨-2474888160752,-912768757058⟩,⟨-231958066996,1706001204064⟩⟩⟩
noncomputable def wholeBoxes52 := wholeStep51.proposed :: wholeBoxes51
theorem wholeAccepted51 : StepValid wholeStep51.shape wholeBoxes51 wholeStep51.proposed := by
  dsimp only [StepValid,wholeStep51]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1200722158768,1207411423547⟩,⟨-936922990717,-754006203570⟩,⟨742541570762,960972753872⟩,⟨8891722861083,15034586377283⟩,⟨-10335252612231,-2205673993199⟩,⟨-5460092800880,5029035489886⟩⟩⟩
noncomputable def wholeBoxes53 := wholeStep52.proposed :: wholeBoxes52
theorem wholeAccepted52 : StepValid wholeStep52.shape wholeBoxes52 wholeStep52.proposed := by
  dsimp only [StepValid,wholeStep52]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1301932689760,1315311219318⟩,⟨-1873845981434,-1508012407140⟩,⟨1485083141524,1921945507743⟩,⟨17783445722172,30069172754557⟩,⟨-20670505224456,-4411347986399⟩,⟨-10915526422470,10058070979769⟩⟩⟩
noncomputable def wholeBoxes54 := wholeStep53.proposed :: wholeBoxes53
theorem wholeAccepted53 : StepValid wholeStep53.shape wholeBoxes53 wholeStep53.proposed := by
  dsimp only [StepValid,wholeStep53]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep54 : Instruction 40 := ⟨.log 0,⟨⟨185799585280,197040400064⟩,⟨-1582505348744,-1260596847443⟩,⟨1241429525071,1623126487519⟩,⟨12588094714308,23948815010701⟩,⟨-16033402981106,-1351456063889⟩,⟨-11614508956516,7092603349697⟩⟩⟩
noncomputable def wholeBoxes55 := wholeStep54.proposed :: wholeBoxes54
theorem wholeAccepted54 : StepValid wholeStep54.shape wholeBoxes54 wholeStep54.proposed := by
  dsimp only [StepValid,wholeStep54]
  exact ⟨by decide,by decide,lc35,by decide⟩
noncomputable def wholeStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨63635432621,68007281872⟩,⟨-539770068762,-421109971360⟩,⟨413027111062,554969813030⟩,⟨4002187780760,7970359897518⟩,⟨-5379998726619,-102814569360⟩,⟨-4359756634900,2463107424557⟩⟩⟩
noncomputable def wholeBoxes56 := wholeStep55.proposed :: wholeBoxes55
theorem wholeAccepted55 : StepValid wholeStep55.shape wholeBoxes55 wholeStep55.proposed := by
  dsimp only [StepValid,wholeStep55]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨379962859868,380542578689⟩,⟨2383386169,21781790193⟩,⟨-23429088998,-926914972⟩,⟨-628470663840,133092264267⟩,⟨-297062452284,632178252779⟩,⟨-650319294186,502148463277⟩⟩⟩
noncomputable def wholeBoxes57 := wholeStep56.proposed :: wholeBoxes56
theorem wholeAccepted56 : StepValid wholeStep56.shape wholeBoxes56 wholeStep56.proposed := by
  dsimp only [StepValid,wholeStep56]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3176847709865,3181694705727⟩,⟨-182394159689,-19896997909⟩,⟨7738076817,196188144418⟩,⟨-1114225355515,5283536204513⟩,⟨-5316163949933,2487414697774⟩,⟨-4204802502086,5469772690568⟩⟩⟩
noncomputable def wholeBoxes58 := wholeStep57.proposed :: wholeBoxes57
theorem wholeAccepted57 : StepValid wholeStep57.shape wholeBoxes57 wholeStep57.proposed := by
  dsimp only [StepValid,wholeStep57]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨183863520204,196795016276⟩,⟨-1573232749361,-1217875617099⟩,⟨1193817886592,1618069962564⟩,⟨11509949487274,23569985060794⟩,⟨-16085478879566,-153650487480⟩,⟨-12870241081574,7663945526609⟩⟩⟩
noncomputable def wholeBoxes59 := wholeStep58.proposed :: wholeBoxes58
theorem wholeAccepted58 : StepValid wholeStep58.shape wholeBoxes58 wholeStep58.proposed := by
  dsimp only [StepValid,wholeStep58]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨369663105484,393835416340⟩,⟨-3155738098105,-2478472464542⟩,⟨2435247411663,3241196450083⟩,⟨24098044201582,47518800071495⟩,⟨-32118881860672,-1505106551369⟩,⟨-24484750038090,14756548876306⟩⟩⟩
noncomputable def wholeBoxes60 := wholeStep59.proposed :: wholeBoxes59
theorem wholeAccepted59 : StepValid wholeStep59.shape wholeBoxes59 wholeStep59.proposed := by
  dsimp only [StepValid,wholeStep59]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨518360403810,526720623782⟩,⟨-31237073868,201460743378⟩,⟨-224419413128,52864615792⟩,⟨-5679796358840,2266487247900⟩,⟨-4080543883432,6363029439830⟩,⟨-7195244193558,6232443465481⟩⟩⟩
noncomputable def wholeBoxes61 := wholeStep60.proposed :: wholeBoxes60
theorem wholeAccepted60 : StepValid wholeStep60.shape wholeBoxes60 wholeStep60.proposed := by
  dsimp only [StepValid,wholeStep60]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨355916249209,364561306515⟩,⟨-32430366157,209156776386⟩,⟨-232992493828,54884105154⟩,⟨-5902973140643,2393068946522⟩,⟨-4280982997140,6616600580871⟩,⟨-7481803041768,6520165459885⟩⟩⟩
noncomputable def wholeBoxes62 := wholeStep61.proposed :: wholeBoxes61
theorem wholeAccepted61 : StepValid wholeStep61.shape wholeBoxes61 wholeStep61.proposed := by
  dsimp only [StepValid,wholeStep61]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨711832498418,729122613030⟩,⟨-64860732314,418313552772⟩,⟨-465984987656,109768210308⟩,⟨-11805946281286,4786137893044⟩,⟨-8561965994280,13233201161742⟩,⟨-14963606083536,13040330919770⟩⟩⟩
noncomputable def wholeBoxes63 := wholeStep62.proposed :: wholeBoxes62
theorem wholeAccepted62 : StepValid wholeStep62.shape wholeBoxes62 wholeStep62.proposed := by
  dsimp only [StepValid,wholeStep62]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1523305995149,1525250711835⟩,⟨-33394844364,31514227764⟩,⟨-36710942240,38608656824⟩,⟨-1236917646576,1303502946062⟩,⟨-1578852871860,1524222028056⟩,⟨-1905736796057,1946190281715⟩⟩⟩
noncomputable def wholeBoxes64 := wholeStep63.proposed :: wholeBoxes63
theorem wholeAccepted63 : StepValid wholeStep63.shape wholeBoxes63 wholeStep63.proposed := by
  dsimp only [StepValid,wholeStep63]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨986200313838,1011444314408⟩,⟨-112120518968,601185802436⟩,⟨-670762085302,177873958509⟩,⟨-17222948034007,7527741544973⟩,⟨-12951535519018,19396799198404⟩,⟨-22054108496349,19411344380875⟩⟩⟩
noncomputable def wholeBoxes65 := wholeStep64.proposed :: wholeBoxes64
theorem wholeAccepted64 : StepValid wholeStep64.shape wholeBoxes64 wholeStep64.proposed := by
  dsimp only [StepValid,wholeStep64]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67626268464,67746436926⟩,⟨13216927206,17234617390⟩,⟨-17677010704,-13015964380⟩,⟨-384800199888,-227235595010⟩,⟨108861435218,301187559586⟩,⟨-206483223398,32116538116⟩⟩⟩
noncomputable def wholeBoxes66 := wholeStep65.proposed :: wholeBoxes65
theorem wholeAccepted65 : StepValid wholeStep65.shape wholeBoxes65 wholeStep65.proposed := by
  dsimp only [StepValid,wholeStep65]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50632777346,51343387655⟩,⟨257715657624,265727531739⟩,⟨32597788514,37601228142⟩,⟨-1365404629209,-1165504668553⟩,⟨-286730525806,-102609708153⟩,⟨-267639071706,-74666554595⟩⟩⟩
noncomputable def wholeBoxes67 := wholeStep66.proposed :: wholeBoxes66
theorem wholeAccepted66 : StepValid wholeStep66.shape wholeBoxes66 wholeStep66.proposed := by
  dsimp only [StepValid,wholeStep66]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2134847569709,2137568568427⟩,⟨-390355808152,-299166462118⟩,⟨294617648568,400375804276⟩,⟨5243292258465,8830132922614⟩,⟨-6938092553300,-2564392261558⟩,⟨-626514837635,4794893591015⟩⟩⟩
noncomputable def wholeBoxes68 := wholeStep67.proposed :: wholeBoxes67
theorem wholeAccepted67 : StepValid wholeStep67.shape wholeBoxes67 wholeStep67.proposed := by
  dsimp only [StepValid,wholeStep67]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2974749456301,2980438528577⟩,⟨-816416961534,-625298932221⟩,⟨615791288096,837373469979⟩,⟨11003012936659,18542492483919⟩,⟨-14587262743469,-5403078394408⟩,⟨-1267854356137,10106791780152⟩⟩⟩
noncomputable def wholeBoxes69 := wholeStep68.proposed :: wholeBoxes68
theorem wholeAccepted68 : StepValid wholeStep68.shape wholeBoxes68 wholeStep68.proposed := by
  dsimp only [StepValid,wholeStep68]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨136987934530,139176164116⟩,⟨659130728175,691510606057⟩,⟨116551270221,141027830758⟩,⟨-3589121104553,-2580553564674⟩,⟨-1341997100059,-342589570112⟩,⟨-748178418151,327213617677⟩⟩⟩
noncomputable def wholeBoxes70 := wholeStep69.proposed :: wholeBoxes69
theorem wholeAccepted69 : StepValid wholeStep69.shape wholeBoxes69 wholeStep69.proposed := by
  dsimp only [StepValid,wholeStep69]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8686299319235,8825053270293⟩,⟨-44548579817367,-41137840173989⟩,⟨-9085311953227,-7274228497436⟩,⟨550711325159431,680978336656047⟩,⟨90282489694292,178179013577582⟩,⟨-8896378943024,66905732248309⟩⟩⟩
noncomputable def wholeBoxes71 := wholeStep70.proposed :: wholeBoxes70
theorem wholeAccepted70 : StepValid wholeStep70.shape wholeBoxes70 wholeStep70.proposed := by
  dsimp only [StepValid,wholeStep70]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨7791123711940,8118195141457⟩,⟨-41880300453898,-32073016116886⟩,⟨-13741371962350,-5096898592328⟩,⟨307003847797200,695939894978421⟩,⟨-35149572806306,347696263466503⟩,⟨-188137123598302,228433906409749⟩⟩⟩
noncomputable def wholeBoxes72 := wholeStep71.proposed :: wholeBoxes71
theorem wholeAccepted71 : StepValid wholeStep71.shape wholeBoxes71 wholeStep71.proposed := by
  dsimp only [StepValid,wholeStep71]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨15582247423880,16236390282914⟩,⟨-83760600907796,-64146032233772⟩,⟨-27482743924700,-10193797184656⟩,⟨614007695594400,1391879789956842⟩,⟨-70299145612612,695392526933006⟩,⟨-376274247196604,456867812819498⟩⟩⟩
noncomputable def wholeBoxes73 := wholeStep72.proposed :: wholeBoxes72
theorem wholeAccepted72 : StepValid wholeStep72.shape wholeBoxes72 wholeStep72.proposed := by
  dsimp only [StepValid,wholeStep72]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10702470597344,10743319721800⟩,⟨-104972894991822,-104176139654566⟩,⟨0,0⟩,⟨2028067813803854,2051378711294242⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes74 := wholeStep73.proposed :: wholeBoxes73
theorem wholeAccepted73 : StepValid wholeStep73.shape wholeBoxes73 wholeStep73.proposed := by
  dsimp only [StepValid,wholeStep73]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9602958969568,9643808094024⟩,⟨-104972894991822,-104176139654566⟩,⟨0,0⟩,⟨2028067813803861,2051378711294240⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes75 := wholeStep74.proposed :: wholeBoxes74
theorem wholeAccepted74 : StepValid wholeStep74.shape wholeBoxes74 wholeStep74.proposed := by
  dsimp only [StepValid,wholeStep74]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep75 : Instruction 40 := ⟨.log 0,⟨⟨2382867281216,2387534528576⟩,⟨-12019099426619,-11877349255562⟩,⟨0,0⟩,⟨99839973091184,106573343585493⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes76 := wholeStep75.proposed :: wholeBoxes75
theorem wholeAccepted75 : StepValid wholeStep75.shape wholeBoxes75 wholeStep75.proposed := by
  dsimp only [StepValid,wholeStep75]
  exact ⟨by decide,by decide,lc36,by decide⟩
noncomputable def wholeStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7286935869360,7376624148997⟩,⟨-43670860664456,-42445594530480⟩,⟨-19679918617269,-19185408727768⟩,⟨494481775974305,517077739804218⟩,⟨271799416961630,282506658885147⟩,⟨101024604758561,105007165597547⟩⟩⟩
noncomputable def wholeBoxes77 := wholeStep76.proposed :: wholeBoxes76
theorem wholeAccepted76 : StepValid wholeStep76.shape wholeBoxes76 wholeStep76.proposed := by
  dsimp only [StepValid,wholeStep76]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6187424241584,6277112521221⟩,⟨-43670860664457,-42445594530479⟩,⟨-19679918617269,-19185408727767⟩,⟨494481775974304,517077739804214⟩,⟨271799416961628,282506658885146⟩,⟨101024604758560,105007165597547⟩⟩⟩
noncomputable def wholeBoxes78 := wholeStep77.proposed :: wholeBoxes77
theorem wholeAccepted77 : StepValid wholeStep77.shape wholeBoxes77 wholeStep77.proposed := by
  dsimp only [StepValid,wholeStep77]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep78 : Instruction 40 := ⟨.log 0,⟨⟨1899574315328,1915397646848⟩,⟨-7760356688161,-7434855528927⟩,⟨-3497141703651,-3360554699073⟩,⟨31841797284192,41611035776229⟩,⟨22926093736846,27477780553546⟩,⟨6572552242515,8388659047148⟩⟩⟩
noncomputable def wholeBoxes79 := wholeStep78.proposed :: wholeBoxes78
theorem wholeAccepted78 : StepValid wholeStep78.shape wholeBoxes78 wholeStep78.proposed := by
  dsimp only [StepValid,wholeStep78]
  exact ⟨by decide,by decide,lc37,by decide⟩
noncomputable def wholeStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨100967634698,101397131429⟩,⟨873596348006,874455341466⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes80 := wholeStep79.proposed :: wholeBoxes79
theorem wholeAccepted79 : StepValid wholeStep79.shape wholeBoxes79 wholeStep79.proposed := by
  dsimp only [StepValid,wholeStep79]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨139157604540,141174729222⟩,⟨674157707917,681575996919⟩,⟨304918108568,306951061833⟩,⟨-1712309844053,-1698693120000⟩,⟨-1543378042884,-1535514561738⟩,⟨-347732631880,-347049799188⟩⟩⟩
noncomputable def wholeBoxes81 := wholeStep80.proposed :: wholeBoxes80
theorem wholeAccepted80 : StepValid wholeStep80.shape wholeBoxes80 wholeStep80.proposed := by
  dsimp only [StepValid,wholeStep80]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4282441596544,4302932175424⟩,⟨-19779456114780,-19312204784489⟩,⟨-3497141703651,-3360554699073⟩,⟨131681770375376,148184379361722⟩,⟨22926093736846,27477780553546⟩,⟨6572552242515,8388659047148⟩⟩⟩
noncomputable def wholeBoxes82 := wholeStep81.proposed :: wholeBoxes81
theorem wholeAccepted81 : StepValid wholeStep81.shape wholeBoxes81 wholeStep81.proposed := by
  dsimp only [StepValid,wholeStep81]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨739326210968,787670832680⟩,⟨-6311476196210,-4956944929084⟩,⟨4870494823326,6482392900166⟩,⟨48196088403164,95037600142990⟩,⟨-64237763721344,-3010213102738⟩,⟨-48969500076180,29513097752612⟩⟩⟩
noncomputable def wholeBoxes83 := wholeStep82.proposed :: wholeBoxes82
theorem wholeAccepted82 : StepValid wholeStep82.shape wholeBoxes82 wholeStep82.proposed := by
  dsimp only [StepValid,wholeStep82]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5021767807512,5090603008104⟩,⟨-26090932310990,-24269149713573⟩,⟨1373353119675,3121838201093⟩,⟨179877858778540,243221979504712⟩,⟨-41311669984498,24467567450808⟩,⟨-42396947833665,37901756799760⟩⟩⟩
noncomputable def wholeBoxes84 := wholeStep83.proposed :: wholeBoxes83
theorem wholeAccepted83 : StepValid wholeStep83.shape wholeBoxes83 wholeStep83.proposed := by
  dsimp only [StepValid,wholeStep83]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨461146571548,469456192392⟩,⟨1583841662553,1819995622108⟩,⟨126114369867,287896399074⟩,⟨-35163996208704,-26178762971918⟩,⟨-2718596589238,4739239777970⟩,⟨-3909853050281,3495305841730⟩⟩⟩
noncomputable def wholeBoxes85 := wholeStep84.proposed :: wholeBoxes84
theorem wholeAccepted84 : StepValid wholeStep84.shape wholeBoxes84 wholeStep84.proposed := by
  dsimp only [StepValid,wholeStep84]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep85 : Instruction 40 := ⟨.mul 88 85,⟨⟨225056286310,225915279770⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes86 := wholeStep85.proposed :: wholeBoxes85
theorem wholeAccepted85 : StepValid wholeStep85.shape wholeBoxes85 wholeStep85.proposed := by
  dsimp only [StepValid,wholeStep85]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep86 : Instruction 40 := ⟨.neg 0,⟨⟨-225915279770,-225056286310⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes87 := wholeStep86.proposed :: wholeBoxes86
theorem wholeAccepted86 : StepValid wholeStep86.shape wholeBoxes86 wholeStep86.proposed := by
  dsimp only [StepValid,wholeStep86]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep87 : Instruction 40 := ⟨.add 89 0,⟨⟨873596348006,874455341466⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes88 := wholeStep87.proposed :: wholeBoxes87
theorem wholeAccepted87 : StepValid wholeStep87.shape wholeBoxes87 wholeStep87.proposed := by
  dsimp only [StepValid,wholeStep87]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep88 : Instruction 40 := ⟨.mul 12 0,⟨⟨1893262519527,1898836054759⟩,⟨-14334009069890,-14202659713135⟩,⟨0,0⟩,⟨126835375642316,132835510026853⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes89 := wholeStep88.proposed :: wholeBoxes88
theorem wholeAccepted88 : StepValid wholeStep88.shape wholeBoxes88 wholeStep88.proposed := by
  dsimp only [StepValid,wholeStep88]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep89 : Instruction 40 := ⟨.neg 91,⟨⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes90 := wholeStep89.proposed :: wholeBoxes89
theorem wholeAccepted89 : StepValid wholeStep89.shape wholeBoxes89 wholeStep89.proposed := by
  dsimp only [StepValid,wholeStep89]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep90 : Instruction 40 := ⟨.add 1 0,⟨⟨793750891751,799324426983⟩,⟨-14334009069890,-14202659713135⟩,⟨0,0⟩,⟨126835375642316,132835510026853⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes91 := wholeStep90.proposed :: wholeBoxes90
theorem wholeAccepted90 : StepValid wholeStep90.shape wholeBoxes90 wholeStep90.proposed := by
  dsimp only [StepValid,wholeStep90]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨36765844641,38802653993⟩,⟨-792627794007,-751182473996⟩,⟨315329944105,317856354168⟩,⟨9214747476197,9919926201805⟩,⟨-6499332721185,-6435979379349⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes92 := wholeStep91.proposed :: wholeBoxes91
theorem wholeAccepted91 : StepValid wholeStep91.shape wholeBoxes91 wholeStep91.proposed := by
  dsimp only [StepValid,wholeStep91]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨497912416189,508258846385⟩,⟨791213868546,1068813148112⟩,⟨441444313972,605752753242⟩,⟨-25949248732507,-16258836770113⟩,⟨-9217929310423,-1696739601379⟩,⟨-3909853050281,3495305841730⟩⟩⟩
noncomputable def wholeBoxes93 := wholeStep92.proposed :: wholeBoxes92
theorem wholeAccepted92 : StepValid wholeStep92.shape wholeBoxes92 wholeStep92.proposed := by
  dsimp only [StepValid,wholeStep92]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep93 : Instruction 40 := ⟨.inv 17,⟨⟨506349041299,507340811276⟩,⟨2518951804351,2559009350623⟩,⟨0,0⟩,⟨2371496934072,4641016220299⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes94 := wholeStep93.proposed :: wholeBoxes93
theorem wholeAccepted93 : StepValid wholeStep93.shape wholeBoxes93 wholeStep93.proposed := by
  dsimp only [StepValid,wholeStep93]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨229299507362,234522718041⟩,⟨1505075272660,1676100209900⟩,⟨203294716963,279508725055⟩,⟨-7274371393507,-367074954578⟩,⟨-3242034639184,628446731954⟩,⟨-1804099173114,1612817233219⟩⟩⟩
noncomputable def wholeBoxes95 := wholeStep94.proposed :: wholeBoxes94
theorem wholeAccepted94 : StepValid wholeStep94.shape wholeBoxes94 wholeStep94.proposed := by
  dsimp only [StepValid,wholeStep94]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-787670832680,-739326210968⟩,⟨4956944929084,6311476196210⟩,⟨-6482392900166,-4870494823326⟩,⟨-95037600142990,-48196088403164⟩,⟨3010213102738,64237763721344⟩,⟨-29513097752612,48969500076180⟩⟩⟩
noncomputable def wholeBoxes96 := wholeStep95.proposed :: wholeBoxes95
theorem wholeAccepted95 : StepValid wholeStep95.shape wholeBoxes95 wholeStep95.proposed := by
  dsimp only [StepValid,wholeStep95]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3494770763864,3563605964456⟩,⟨-14822511185696,-13000728588279⟩,⟨-9979534603817,-8231049522399⟩,⟨36644170232386,99988290958558⟩,⟨25936306839584,91715544274890⟩,⟨-22940545510097,57358159123328⟩⟩⟩
noncomputable def wholeBoxes97 := wholeStep96.proposed :: wholeBoxes96
theorem wholeAccepted96 : StepValid wholeStep96.shape wholeBoxes96 wholeStep96.proposed := by
  dsimp only [StepValid,wholeStep96]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨442309035784,457558696404⟩,⟨239617879588,563630274184⟩,⟨-312174237715,-46894001245⟩,⟨-19288580278806,-8503598950261⟩,⟨-12043850495036,-1756722959096⟩,⟨-9644522713716,1696272181383⟩⟩⟩
noncomputable def wholeBoxes98 := wholeStep97.proposed :: wholeBoxes97
theorem wholeAccepted97 : StepValid wholeStep97.shape wholeBoxes97 wholeStep97.proposed := by
  dsimp only [StepValid,wholeStep97]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨327772106914,331806356276⟩,⟨1932735283200,1940466224334⟩,⟨873596348006,874455341466⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes99 := wholeStep98.proposed :: wholeBoxes98
theorem wholeAccepted98 : StepValid wholeStep98.shape wholeBoxes98 wholeStep98.proposed := by
  dsimp only [StepValid,wholeStep98]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-331806356276,-327772106914⟩,⟨-1940466224334,-1932735283200⟩,⟨-874455341466,-873596348006⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes100 := wholeStep99.proposed :: wholeBoxes99
theorem wholeAccepted99 : StepValid wholeStep99.shape wholeBoxes99 wholeStep99.proposed := by
  dsimp only [StepValid,wholeStep99]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨767705271500,771739520862⟩,⟨-1940466224334,-1932735283200⟩,⟨-874455341466,-873596348006⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes101 := wholeStep100.proposed :: wholeBoxes100
theorem wholeAccepted100 : StepValid wholeStep100.shape wholeBoxes100 wholeStep100.proposed := by
  dsimp only [StepValid,wholeStep100]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1326328143007,1344404210831⟩,⟨-8827317644425,-8530289128150⟩,⟨-3977958991601,-3855690685921⟩,⟨48370867117783,56598128955413⟩,⟨31621144796899,35461074624511⟩,⟨9929244359733,11450582132024⟩⟩⟩
noncomputable def wholeBoxes102 := wholeStep101.proposed :: wholeBoxes101
theorem wholeAccepted101 : StepValid wholeStep101.shape wholeBoxes101 wholeStep101.proposed := by
  dsimp only [StepValid,wholeStep101]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1344404210831,-1326328143007⟩,⟨8530289128150,8827317644425⟩,⟨3855690685921,3977958991601⟩,⟨-56598128955413,-48370867117783⟩,⟨-35461074624511,-31621144796899⟩,⟨-11450582132024,-9929244359733⟩⟩⟩
noncomputable def wholeBoxes103 := wholeStep102.proposed :: wholeBoxes102
theorem wholeAccepted102 : StepValid wholeStep102.shape wholeBoxes102 wholeStep102.proposed := by
  dsimp only [StepValid,wholeStep102]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-244892583055,-226816515231⟩,⟨8530289128150,8827317644425⟩,⟨3855690685921,3977958991601⟩,⟨-56598128955413,-48370867117783⟩,⟨-35461074624511,-31621144796899⟩,⟨-11450582132024,-9929244359733⟩⟩⟩
noncomputable def wholeBoxes104 := wholeStep103.proposed :: wholeBoxes103
theorem wholeAccepted103 : StepValid wholeStep103.shape wholeBoxes103 wholeStep103.proposed := by
  dsimp only [StepValid,wholeStep103]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-11888141842,-10505941911⟩,⟨421784166074,458171018883⟩,⟨81209142252,103000875835⟩,⟨-4885383195697,-4246446913217⟩,⟨1412467731966,1837122060132⟩,⟨2507606114148,2703806626532⟩⟩⟩
noncomputable def wholeBoxes105 := wholeStep104.proposed :: wholeBoxes104
theorem wholeAccepted104 : StepValid wholeStep104.shape wholeBoxes104 wholeStep104.proposed := by
  dsimp only [StepValid,wholeStep104]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨430420893942,447052754493⟩,⟨661402045662,1021801293067⟩,⟨-230965095463,56106874590⟩,⟨-24173963474503,-12750045863478⟩,⟨-10631382763070,80399101036⟩,⟨-7136916599568,4400078807915⟩⟩⟩
noncomputable def wholeBoxes106 := wholeStep105.proposed :: wholeBoxes105
theorem wholeAccepted105 : StepValid wholeStep105.shape wholeBoxes105 wholeStep105.proposed := by
  dsimp only [StepValid,wholeStep105]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-101397131429,-100967634698⟩,⟨-874455341466,-873596348006⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes107 := wholeStep106.proposed :: wholeBoxes106
theorem wholeAccepted106 : StepValid wholeStep106.shape wholeBoxes106 wholeStep106.proposed := by
  dsimp only [StepValid,wholeStep106]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4676732221,4922253936⟩,⟨28185657211,30578247337⟩,⟨40110970503,40321203045⟩,⟨-318532222978,-307288468353⟩,⟨245652667759,246764997182⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes108 := wholeStep107.proposed :: wholeBoxes107
theorem wholeAccepted107 : StepValid wholeStep107.shape wholeBoxes107 wholeStep107.proposed := by
  dsimp only [StepValid,wholeStep107]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨10135438235,10688428330⟩,⟨7277431820,15879267610⟩,⟨86928702539,87555476515⟩,⟨-935531581305,-797798171862⟩,⟨91616271808,102543659135⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes109 := wholeStep108.proposed :: wholeBoxes108
theorem wholeAccepted108 : StepValid wholeStep108.shape wholeBoxes108 wholeStep108.proposed := by
  dsimp only [StepValid,wholeStep108]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1450780685559,1468532291070⟩,⟨-7315217298471,-7014949448110⟩,⟨-1370781807805,-1301957207965⟩,⟨99653231124713,106771354091844⟩,⟨20947365612086,22669329911927⟩,⟨4638180098373,5061765400982⟩⟩⟩
noncomputable def wholeBoxes110 := wholeStep109.proposed :: wholeBoxes109
theorem wholeAccepted109 : StepValid wholeStep109.shape wholeBoxes109 wholeStep109.proposed := by
  dsimp only [StepValid,wholeStep109]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨13373481152,14275703637⟩,⟨-61509325214,-43455993008⟩,⟨101374989349,104939442879⟩,⟨-542195042450,-107605815593⟩,⟨-288335740672,-205897937098⟩,⟨-175558780804,-156662813412⟩⟩⟩
noncomputable def wholeBoxes111 := wholeStep110.proposed :: wholeBoxes110
theorem wholeAccepted110 : StepValid wholeStep110.shape wholeBoxes110 wholeStep110.proposed := by
  dsimp only [StepValid,wholeStep110]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-14275703637,-13373481152⟩,⟨43455993008,61509325214⟩,⟨-104939442879,-101374989349⟩,⟨107605815593,542195042450⟩,⟨205897937098,288335740672⟩,⟨156662813412,175558780804⟩⟩⟩
noncomputable def wholeBoxes112 := wholeStep111.proposed :: wholeBoxes111
theorem wholeAccepted111 : StepValid wholeStep111.shape wholeBoxes111 wholeStep111.proposed := by
  dsimp only [StepValid,wholeStep111]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-115672835066,-114341115850⟩,⟨-830999348458,-812087022792⟩,⟨-104939442879,-101374989349⟩,⟨2306629071145,2741218298002⟩,⟨205897937098,288335740672⟩,⟨156662813412,175558780804⟩⟩⟩
noncomputable def wholeBoxes113 := wholeStep112.proposed :: wholeBoxes112
theorem wholeAccepted112 : StepValid wholeStep112.shape wholeBoxes112 wholeStep112.proposed := by
  dsimp only [StepValid,wholeStep112]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨87986615055,92981660061⟩,⟨-608663856406,-567724368920⟩,⟨584869241306,606011901358⟩,⟨3223236848552,3899440468971⟩,⟨-3544307725685,-3095814901454⟩,⟨-2476885659955,-2262844047692⟩⟩⟩
noncomputable def wholeBoxes114 := wholeStep113.proposed :: wholeBoxes113
theorem wholeAccepted113 : StepValid wholeStep113.shape wholeBoxes113 wholeStep113.proposed := by
  dsimp only [StepValid,wholeStep113]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨116096345399,124188382213⟩,⟨-1431566102528,-1310459270708⟩,⟨655799731969,705216041972⟩,⟨19471804760255,22336506607537⟩,⟨-6417211315941,-5140463470068⟩,⟨-4448073910182,-3942831006380⟩⟩⟩
noncomputable def wholeBoxes115 := wholeStep114.proposed :: wholeBoxes114
theorem wholeAccepted114 : StepValid wholeStep114.shape wholeBoxes114 wholeStep114.proposed := by
  dsimp only [StepValid,wholeStep114]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-124188382213,-116096345399⟩,⟨1310459270708,1431566102528⟩,⟨-705216041972,-655799731969⟩,⟨-22336506607537,-19471804760255⟩,⟨5140463470068,6417211315941⟩,⟨3942831006380,4448073910182⟩⟩⟩
noncomputable def wholeBoxes116 := wholeStep115.proposed :: wholeBoxes115
theorem wholeAccepted115 : StepValid wholeStep115.shape wholeBoxes115 wholeStep115.proposed := by
  dsimp only [StepValid,wholeStep115]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨975323245563,983415282377⟩,⟨1310459270708,1431566102528⟩,⟨-705216041972,-655799731969⟩,⟨-22336506607537,-19471804760255⟩,⟨5140463470068,6417211315941⟩,⟨3942831006380,4448073910182⟩⟩⟩
noncomputable def wholeBoxes117 := wholeStep116.proposed :: wholeBoxes116
theorem wholeAccepted116 : StepValid wholeStep116.shape wholeBoxes116 wholeStep116.proposed := by
  dsimp only [StepValid,wholeStep116]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨123439937401,126268229181⟩,⟨763868280651,793418810972⟩,⟨179929916622,191540353072⟩,⟨-2792466606820,-2196413703630⟩,⟨-803559065216,-540573350895⟩,⟨-205749795195,-100463270817⟩⟩⟩
noncomputable def wholeBoxes118 := wholeStep117.proposed :: wholeBoxes117
theorem wholeAccepted117 : StepValid wholeStep117.shape wholeBoxes117 wholeStep117.proposed := by
  dsimp only [StepValid,wholeStep117]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11890634390,12169225349⟩,⟨168902145292,174848629422⟩,⟨21084505354,22080062752⟩,⟨622823500673,776376282905⟩,⟨89080823656,115800519384⟩,⟨-18245361264,-12552326053⟩⟩⟩
noncomputable def wholeBoxes119 := wholeStep118.proposed :: wholeBoxes118
theorem wholeAccepted118 : StepValid wholeStep118.shape wholeBoxes118 wholeStep118.proposed := by
  dsimp only [StepValid,wholeStep118]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨168513731379,179701866916⟩,⟨1466626954924,1888268862665⟩,⟨-5365768442,215813816745⟩,⟨-11173071131207,7162127299891⟩,⟨-5568077669570,6610506916979⟩,⟨-5537773481052,4487693855452⟩⟩⟩
noncomputable def wholeBoxes120 := wholeStep119.proposed :: wholeBoxes119
theorem wholeAccepted119 : StepValid wholeStep119.shape wholeBoxes119 wholeStep119.proposed := by
  dsimp only [StepValid,wholeStep119]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-179701866916,-168513731379⟩,⟨-1888268862665,-1466626954924⟩,⟨-215813816745,5365768442⟩,⟨-7162127299891,11173071131207⟩,⟨-6610506916979,5568077669570⟩,⟨-4487693855452,5537773481052⟩⟩⟩
noncomputable def wholeBoxes121 := wholeStep120.proposed :: wholeBoxes120
theorem wholeAccepted120 : StepValid wholeStep120.shape wholeBoxes120 wholeStep120.proposed := by
  dsimp only [StepValid,wholeStep120]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨49597640446,66008986662⟩,⟨-383193590005,209473254976⟩,⟨-12519099782,284874493497⟩,⟨-14436498693398,10805996176629⟩,⟨-9852541556163,6196524401524⟩,⟨-6291793028566,7150590714271⟩⟩⟩
noncomputable def wholeBoxes122 := wholeStep121.proposed :: wholeBoxes121
theorem wholeAccepted121 : StepValid wholeStep121.shape wholeBoxes121 wholeStep121.proposed := by
  dsimp only [StepValid,wholeStep121]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨26920713009065,28284506462296⟩,⟨-260511149282112,-216188631087804⟩,⟨-99518129552444,-65237027329270⟩,⟨2379559170087434,4221547506164074⟩,⟨467430169372134,2077551257645051⟩,⟨-500027496254959,1094583399803479⟩⟩⟩
noncomputable def wholeBoxes123 := wholeStep122.proposed :: wholeBoxes122
theorem wholeAccepted122 : StepValid wholeStep122.shape wholeBoxes122 wholeStep122.proposed := by
  dsimp only [StepValid,wholeStep122]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13858351072,14500679482⟩,⟨171515880984,182232885456⟩,⟨40400732622,43993097642⟩,⟨419995443178,651904410047⟩,⟨65445012004,155056802384⟩,⟨11632642057,44176935252⟩⟩⟩
noncomputable def wholeBoxes124 := wholeStep123.proposed :: wholeBoxes123
theorem wholeAccepted123 : StepValid wholeStep123.shape wholeBoxes123 wholeStep123.proposed := by
  dsimp only [StepValid,wholeStep123]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨339311274718,373024306570⟩,⟨763740109723,1963007233766⟩,⟨-323292598311,309451413095⟩,⟨-46078688399301,4997250256745⟩,⟨-19423651388831,13267931288229⟩,⟨-14273428876665,10777947373864⟩⟩⟩
noncomputable def wholeBoxes125 := wholeStep124.proposed :: wholeBoxes124
theorem wholeAccepted124 : StepValid wholeStep124.shape wholeBoxes124 wholeStep124.proposed := by
  dsimp only [StepValid,wholeStep124]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-373024306570,-339311274718⟩,⟨-1963007233766,-763740109723⟩,⟨-309451413095,323292598311⟩,⟨-4997250256745,46078688399301⟩,⟨-13267931288229,19423651388831⟩,⟨-10777947373864,14273428876665⟩⟩⟩
noncomputable def wholeBoxes126 := wholeStep125.proposed :: wholeBoxes125
theorem wholeAccepted125 : StepValid wholeStep125.shape wholeBoxes125 wholeStep125.proposed := by
  dsimp only [StepValid,wholeStep125]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨57396587372,107741479775⟩,⟨-1301605188104,258061183344⟩,⟨-540416508558,379399472901⟩,⟨-29171213731248,33328642535823⟩,⟨-23899314051299,19504050489867⟩,⟨-17914863973432,18673507684580⟩⟩⟩
noncomputable def wholeBoxes127 := wholeStep126.proposed :: wholeBoxes126
theorem wholeAccepted126 : StepValid wholeStep126.shape wholeBoxes126 wholeStep126.proposed := by
  dsimp only [StepValid,wholeStep126]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨240125239238,242571860651⟩,⟨1547754055923,1556031338385⟩,⟨304918108568,306951061833⟩,⟨-3911333099605,-3897716375552⟩,⟨-1543378042884,-1535514561738⟩,⟨-347732631880,-347049799188⟩⟩⟩
noncomputable def wholeBoxes128 := wholeStep127.proposed :: wholeBoxes127
theorem wholeAccepted127 : StepValid wholeStep127.shape wholeBoxes127 wholeStep127.proposed := by
  dsimp only [StepValid,wholeStep127]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1708130453392,-1620439032101⟩,⟨-5600578191163,-2696938049693⟩,⟨-489551535624,1454606479942⟩,⟨-18986516617947,103237811930680⟩,⟨-56796687870712,40419005184533⟩,⟨-43964286557174,47423961851357⟩⟩⟩
noncomputable def wholeBoxes129 := wholeStep128.proposed :: wholeBoxes128
theorem wholeAccepted128 : StepValid wholeStep128.shape wholeBoxes128 wholeStep128.proposed := by
  dsimp only [StepValid,wholeStep128]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-196162188841,-181923399108⟩,⟨-1875776364527,-1428554097745⟩,⟨-353784994907,-98129817669⟩,⟨-7026253582843,12446746119273⟩,⟨-7054775018993,6498405333002⟩,⟨-5071374974630,6272620205136⟩⟩⟩
noncomputable def wholeBoxes130 := wholeStep129.proposed :: wholeBoxes129
theorem wholeAccepted129 : StepValid wholeStep129.shape wholeBoxes129 wholeStep129.proposed := by
  dsimp only [StepValid,wholeStep129]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨43963050397,60648461543⟩,⟨-328022308604,127477240640⟩,⟨-48866886339,208821244164⟩,⟨-10937586682448,8549029743721⟩,⟨-8598153061877,4962890771264⟩,⟨-5419107606510,5925570405948⟩⟩⟩
noncomputable def wholeBoxes131 := wholeStep130.proposed :: wholeBoxes130
theorem wholeAccepted130 : StepValid wholeStep130.shape wholeBoxes130 wholeStep130.proposed := by
  dsimp only [StepValid,wholeStep130]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨2589090675,6468240737⟩,⟨-115690894680,36019005778⟩,⟨-33670560190,50692118955⟩,⟨-3661875726712,3967013498115⟩,⟨-2869705416753,2033325024998⟩,⟨-1972085434970,2018347922656⟩⟩⟩
noncomputable def wholeBoxes132 := wholeStep131.proposed :: wholeBoxes131
theorem wholeAccepted131 : StepValid wholeStep131.shape wholeBoxes131 wholeStep131.proposed := by
  dsimp only [StepValid,wholeStep131]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨1757825703,3345336052⟩,⟨-36187063178,14063150096⟩,⟨-5390941582,23036931810⟩,⟨-1282684359565,1138840410176⟩,⟨-1073136048784,595922112694⟩,⟨-616391813810,733021881206⟩⟩⟩
noncomputable def wholeBoxes133 := wholeStep132.proposed :: wholeBoxes132
theorem wholeAccepted132 : StepValid wholeStep132.shape wholeBoxes132 wholeStep132.proposed := by
  dsimp only [StepValid,wholeStep132]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨3036912454,5827722637⟩,⟨-86650849575,12612276309⟩,⟨-20031539899,34758718861⟩,⟨-2382101589385,2621331237104⟩,⟨-2040121964712,1274872501753⟩,⟨-1209817908927,1336772623424⟩⟩⟩
noncomputable def wholeBoxes134 := wholeStep133.proposed :: wholeBoxes133
theorem wholeAccepted133 : StepValid wholeStep133.shape wholeBoxes133 wholeStep133.proposed := by
  dsimp only [StepValid,wholeStep133]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-5827722637,-3036912454⟩,⟨-12612276309,86650849575⟩,⟨-34758718861,20031539899⟩,⟨-2621331237104,2382101589385⟩,⟨-1274872501753,2040121964712⟩,⟨-1336772623424,1209817908927⟩⟩⟩
noncomputable def wholeBoxes135 := wholeStep134.proposed :: wholeBoxes134
theorem wholeAccepted134 : StepValid wholeStep134.shape wholeBoxes134 wholeStep134.proposed := by
  dsimp only [StepValid,wholeStep134]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨-3238631962,3431328283⟩,⟨-128303170989,122669855353⟩,⟨-68429279051,70723658854⟩,⟨-6283206963816,6349115087500⟩,⟨-4144577918506,4073446989710⟩,⟨-3308858058394,3228165831583⟩⟩⟩
noncomputable def wholeBoxes136 := wholeStep135.proposed :: wholeBoxes135
theorem wholeAccepted135 : StepValid wholeStep135.shape wholeBoxes135 wholeStep135.proposed := by
  dsimp only [StepValid,wholeStep135]
  exact ⟨by decide,by decide⟩
noncomputable def wholeProgram : List (Instruction 40) := [wholeStep0,wholeStep1,wholeStep2,wholeStep3,wholeStep4,wholeStep5,wholeStep6,wholeStep7,wholeStep8,wholeStep9,wholeStep10,wholeStep11,wholeStep12,wholeStep13,wholeStep14,wholeStep15,wholeStep16,wholeStep17,wholeStep18,wholeStep19,wholeStep20,wholeStep21,wholeStep22,wholeStep23,wholeStep24,wholeStep25,wholeStep26,wholeStep27,wholeStep28,wholeStep29,wholeStep30,wholeStep31,wholeStep32,wholeStep33,wholeStep34,wholeStep35,wholeStep36,wholeStep37,wholeStep38,wholeStep39,wholeStep40,wholeStep41,wholeStep42,wholeStep43,wholeStep44,wholeStep45,wholeStep46,wholeStep47,wholeStep48,wholeStep49,wholeStep50,wholeStep51,wholeStep52,wholeStep53,wholeStep54,wholeStep55,wholeStep56,wholeStep57,wholeStep58,wholeStep59,wholeStep60,wholeStep61,wholeStep62,wholeStep63,wholeStep64,wholeStep65,wholeStep66,wholeStep67,wholeStep68,wholeStep69,wholeStep70,wholeStep71,wholeStep72,wholeStep73,wholeStep74,wholeStep75,wholeStep76,wholeStep77,wholeStep78,wholeStep79,wholeStep80,wholeStep81,wholeStep82,wholeStep83,wholeStep84,wholeStep85,wholeStep86,wholeStep87,wholeStep88,wholeStep89,wholeStep90,wholeStep91,wholeStep92,wholeStep93,wholeStep94,wholeStep95,wholeStep96,wholeStep97,wholeStep98,wholeStep99,wholeStep100,wholeStep101,wholeStep102,wholeStep103,wholeStep104,wholeStep105,wholeStep106,wholeStep107,wholeStep108,wholeStep109,wholeStep110,wholeStep111,wholeStep112,wholeStep113,wholeStep114,wholeStep115,wholeStep116,wholeStep117,wholeStep118,wholeStep119,wholeStep120,wholeStep121,wholeStep122,wholeStep123,wholeStep124,wholeStep125,wholeStep126,wholeStep127,wholeStep128,wholeStep129,wholeStep130,wholeStep131,wholeStep132,wholeStep133,wholeStep134,wholeStep135]
theorem wholeAccepted : Accepted wholeProgram wholeInitial :=
  ⟨wholeAccepted0,⟨wholeAccepted1,⟨wholeAccepted2,⟨wholeAccepted3,⟨wholeAccepted4,⟨wholeAccepted5,⟨wholeAccepted6,⟨wholeAccepted7,⟨wholeAccepted8,⟨wholeAccepted9,⟨wholeAccepted10,⟨wholeAccepted11,⟨wholeAccepted12,⟨wholeAccepted13,⟨wholeAccepted14,⟨wholeAccepted15,⟨wholeAccepted16,⟨wholeAccepted17,⟨wholeAccepted18,⟨wholeAccepted19,⟨wholeAccepted20,⟨wholeAccepted21,⟨wholeAccepted22,⟨wholeAccepted23,⟨wholeAccepted24,⟨wholeAccepted25,⟨wholeAccepted26,⟨wholeAccepted27,⟨wholeAccepted28,⟨wholeAccepted29,⟨wholeAccepted30,⟨wholeAccepted31,⟨wholeAccepted32,⟨wholeAccepted33,⟨wholeAccepted34,⟨wholeAccepted35,⟨wholeAccepted36,⟨wholeAccepted37,⟨wholeAccepted38,⟨wholeAccepted39,⟨wholeAccepted40,⟨wholeAccepted41,⟨wholeAccepted42,⟨wholeAccepted43,⟨wholeAccepted44,⟨wholeAccepted45,⟨wholeAccepted46,⟨wholeAccepted47,⟨wholeAccepted48,⟨wholeAccepted49,⟨wholeAccepted50,⟨wholeAccepted51,⟨wholeAccepted52,⟨wholeAccepted53,⟨wholeAccepted54,⟨wholeAccepted55,⟨wholeAccepted56,⟨wholeAccepted57,⟨wholeAccepted58,⟨wholeAccepted59,⟨wholeAccepted60,⟨wholeAccepted61,⟨wholeAccepted62,⟨wholeAccepted63,⟨wholeAccepted64,⟨wholeAccepted65,⟨wholeAccepted66,⟨wholeAccepted67,⟨wholeAccepted68,⟨wholeAccepted69,⟨wholeAccepted70,⟨wholeAccepted71,⟨wholeAccepted72,⟨wholeAccepted73,⟨wholeAccepted74,⟨wholeAccepted75,⟨wholeAccepted76,⟨wholeAccepted77,⟨wholeAccepted78,⟨wholeAccepted79,⟨wholeAccepted80,⟨wholeAccepted81,⟨wholeAccepted82,⟨wholeAccepted83,⟨wholeAccepted84,⟨wholeAccepted85,⟨wholeAccepted86,⟨wholeAccepted87,⟨wholeAccepted88,⟨wholeAccepted89,⟨wholeAccepted90,⟨wholeAccepted91,⟨wholeAccepted92,⟨wholeAccepted93,⟨wholeAccepted94,⟨wholeAccepted95,⟨wholeAccepted96,⟨wholeAccepted97,⟨wholeAccepted98,⟨wholeAccepted99,⟨wholeAccepted100,⟨wholeAccepted101,⟨wholeAccepted102,⟨wholeAccepted103,⟨wholeAccepted104,⟨wholeAccepted105,⟨wholeAccepted106,⟨wholeAccepted107,⟨wholeAccepted108,⟨wholeAccepted109,⟨wholeAccepted110,⟨wholeAccepted111,⟨wholeAccepted112,⟨wholeAccepted113,⟨wholeAccepted114,⟨wholeAccepted115,⟨wholeAccepted116,⟨wholeAccepted117,⟨wholeAccepted118,⟨wholeAccepted119,⟨wholeAccepted120,⟨wholeAccepted121,⟨wholeAccepted122,⟨wholeAccepted123,⟨wholeAccepted124,⟨wholeAccepted125,⟨wholeAccepted126,⟨wholeAccepted127,⟨wholeAccepted128,⟨wholeAccepted129,⟨wholeAccepted130,⟨wholeAccepted131,⟨wholeAccepted132,⟨wholeAccepted133,⟨wholeAccepted134,⟨wholeAccepted135,True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
noncomputable def whole_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨49597640446,66008986662⟩,⟨-383193590005,209473254976⟩,⟨-12519099782,284874493497⟩,⟨-14436498693398,10805996176629⟩,⟨-9852541556163,6196524401524⟩,⟨-6291793028566,7150590714271⟩⟩
theorem whole_m11_eq : (finalBoxes wholeProgram wholeInitial).getD 14 (zeroBox 40)=whole_m11 := rfl
noncomputable def whole_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨-3238631962,3431328283⟩,⟨-128303170989,122669855353⟩,⟨-68429279051,70723658854⟩,⟨-6283206963816,6349115087500⟩,⟨-4144577918506,4073446989710⟩,⟨-3308858058394,3228165831583⟩⟩
theorem whole_kdet_eq : (finalBoxes wholeProgram wholeInitial).getD 0 (zeroBox 40)=whole_kdet := rfl
theorem sameShape : shapes centerProgram=shapes wholeProgram := by decide
theorem kernelShape : shapes wholeProgram =
    shapes CorrectionFactorizedProgramKernel.kernelProgram := by decide
attribute [local irreducible] wholeProgram centerProgram
noncomputable def inputJets (u rho : ℝ) : List BivariateJet2 :=
  [BivariateJet2.affineA (105/1024) u, BivariateJet2.affineZ (611/5120) rho,
    BivariateJet2.const 1, BivariateJet2.const 2]
noncomputable def outputJet_m11 (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 14 zeroJet
theorem output_value_m11 (u rho t : ℝ) : (outputJet_m11 u rho).value t =
    Correction.Natural.m11 (105/1024+t*(u-(105/1024))) ((105/1024+t*(u-(105/1024)))+(611/5120+t*(rho-(611/5120)))*(1/2-(105/1024+t*(u-(105/1024))))) := by
  exact CorrectionFactorizedProgramKernel.output_value_m11_of_shapes wholeProgram kernelShape (105/1024) (611/5120) u rho t
theorem output_value_one_m11 (u rho : ℝ) : (outputJet_m11 u rho).value 1 =
    Correction.Natural.m11 u (u+rho*(1/2-u)) := by simp [output_value_m11]
noncomputable def outputJet_kdet (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 0 zeroJet
theorem output_value_kdet (u rho t : ℝ) : (outputJet_kdet u rho).value t =
    Correction.Natural.kdet (105/1024+t*(u-(105/1024))) ((105/1024+t*(u-(105/1024)))+(611/5120+t*(rho-(611/5120)))*(1/2-(105/1024+t*(u-(105/1024))))) := by
  exact CorrectionFactorizedProgramKernel.output_value_kdet_of_shapes wholeProgram kernelShape (105/1024) (611/5120) u rho t
theorem output_value_one_kdet (u rho : ℝ) : (outputJet_kdet u rho).value 1 =
    Correction.Natural.kdet u (u+rho*(1/2-u)) := by simp [output_value_kdet]

private theorem center_A (x : ℝ) :
    (⟨⟨112742891520,112742891520⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩ : DyadicBivariateJetEnclosure 40).Contains (BivariateJet2.affineA (105/1024) x) 0 := by
  apply DyadicBivariateJetEnclosure.contains_coordinateA
  norm_num [DyadicInterval.Contains,DyadicInterval.scale]
private theorem whole_A {x t : ℝ} (hx : x∈Icc (131/1280:ℝ) (263/2560)) (ht : t∈Icc (0:ℝ) 1) :
    (⟨⟨112528143155,112957639885⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩ : DyadicBivariateJetEnclosure 40).Contains (BivariateJet2.affineA (105/1024) x) t := by
  apply DyadicBivariateJetEnclosure.contains_coordinateA
  change (⟨112528143155,112957639885⟩ : DyadicInterval 40).Contains ((Jet2.segment (105/1024) x).value t)
  apply DyadicInterval.contains_segment _ _ ht
  · norm_num [DyadicInterval.Contains,DyadicInterval.scale]
  · norm_num [DyadicInterval.Contains,DyadicInterval.scale]
    constructor <;> linarith [hx.1,hx.2]
private theorem center_Z (x : ℝ) :
    (⟨⟨131211250892,131211250893⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩ : DyadicBivariateJetEnclosure 40).Contains (BivariateJet2.affineZ (611/5120) x) 0 := by
  apply DyadicBivariateJetEnclosure.contains_coordinateZ
  norm_num [DyadicInterval.Contains,DyadicInterval.scale]
private theorem whole_Z {x t : ℝ} (hx : x∈Icc (301/2560:ℝ) (31/256)) (ht : t∈Icc (0:ℝ) 1) :
    (⟨⟨129278515609,133143986176⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩ : DyadicBivariateJetEnclosure 40).Contains (BivariateJet2.affineZ (611/5120) x) t := by
  apply DyadicBivariateJetEnclosure.contains_coordinateZ
  change (⟨129278515609,133143986176⟩ : DyadicInterval 40).Contains ((Jet2.segment (611/5120) x).value t)
  apply DyadicInterval.contains_segment _ _ ht
  · norm_num [DyadicInterval.Contains,DyadicInterval.scale]
  · norm_num [DyadicInterval.Contains,DyadicInterval.scale]
    constructor <;> linarith [hx.1,hx.2]
theorem initial_center (a z : ℝ) : RegistersContain centerInitial (inputJets a z) 0 := by
  simpa [centerInitial,inputJets,DyadicBivariateJetEnclosure.const,DyadicInterval.ofInt,DyadicInterval.scale] using
    ((((RegistersContain.nil 40 0).cons (DyadicBivariateJetEnclosure.contains_const 40 2 0)).cons
      (DyadicBivariateJetEnclosure.contains_const 40 1 0)).cons (center_Z z)).cons (center_A a)

theorem initial_whole {a z : ℝ} (ha : a ∈ Icc (131/1280:ℝ) (263/2560))
    (hz : z ∈ Icc (301/2560:ℝ) (31/256)) :
    ∀ t ∈ Icc (0:ℝ) 1, RegistersContain wholeInitial (inputJets a z) t := by
  intro t ht
  simpa [wholeInitial,inputJets,DyadicBivariateJetEnclosure.const,DyadicInterval.ofInt,DyadicInterval.scale] using
    ((((RegistersContain.nil 40 t).cons (DyadicBivariateJetEnclosure.contains_const 40 2 t)).cons
      (DyadicBivariateJetEnclosure.contains_const 40 1 t)).cons (whole_Z hz ht)).cons (whole_A ha ht)

theorem initial_sound (a z : ℝ) : ∀ i, ((inputJets a z).getD i zeroJet).DirectionalSoundOn
    (a-105/1024) (z-611/5120) (Icc (0:ℝ) 1) := by
  intro i t ht
  have hconst (c : ℝ) : (BivariateJet2.const c).DirectionalSoundAt (a-105/1024) (z-611/5120) t := by
    simpa only [BivariateJet2.DirectionalSoundAt,BivariateJet2.projection_const] using Jet2.soundAt_const c t
  have h : RegistersSound (inputJets a z) (a-105/1024) (z-611/5120) t :=
    ((((RegistersSound.nil _ _ t).cons (hconst 2)).cons (hconst 1)).cons
      (BivariateJet2.soundOn_affineZ (611/5120) z (a-105/1024) _ t ht)).cons
      (BivariateJet2.soundOn_affineA (105/1024) a (z-611/5120) _ t ht)
  exact h i

theorem taylor_positive_m11 : 0 < BivariateJetEnclosure.taylorLower
    center_m11.toReal whole_m11.toReal (1/5120) (9/5120) := by
  norm_num [BivariateJetEnclosure.taylorLower,JetBounds.Interval.magnitude,
    DyadicBivariateJetEnclosure.toReal,DyadicInterval.toReal,DyadicInterval.scale,center_m11,whole_m11]
theorem positive_m11 {a z : ℝ} (ha : a∈Icc (131/1280:ℝ) (263/2560))
    (hz : z∈Icc (301/2560:ℝ) (31/256)) : 0 < Correction.Natural.m11 a (a+z*(1/2-a)) := by
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
theorem positive_kdet {a z : ℝ} (ha : a∈Icc (131/1280:ℝ) (263/2560))
    (hz : z∈Icc (301/2560:ℝ) (31/256)) : 0 < Correction.Natural.kdet a (a+z*(1/2-a)) := by
  have hp := value_pos_of_accepted_taylor centerProgram wholeProgram 0 sameShape
    (initial_center a z) (initial_whole ha hz) (initial_sound a z) centerAccepted wholeAccepted
    (show (0:ℝ)≤1/5120 by norm_num) (show (0:ℝ)≤9/5120 by norm_num)
    (by rw [abs_le]; constructor <;> linarith [ha.1,ha.2])
    (by rw [abs_le]; constructor <;> linarith [hz.1,hz.2])
    (by rw [center_kdet_eq,whole_kdet_eq]; exact taylor_positive_kdet)
  change 0 < (outputJet_kdet a z).value 1 at hp
  simpa only [output_value_one_kdet] using hp

theorem _root_.solution {u rho : ℝ} (hu : u∈Icc (131/1280:ℝ) (263/2560))
    (hr : rho∈Icc (301/2560:ℝ) (31/256)) (hr1 : rho < 1) :
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




end GeneralCK.Certificates.LaneCB.RB2Cell000057
end

