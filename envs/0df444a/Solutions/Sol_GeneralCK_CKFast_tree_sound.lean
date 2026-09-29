-- Prove2me | solution 1 for GeneralCK.CKFast.tree_sound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T04:53:20.649652+00:00
-- url     : https://prove2.me/submissions/a2af234e-b114-442f-8825-a7a0263466b7

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
import Definitions.Def_GeneralCK_CKFast_eval

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



/-!
# Soundness of the computing correction-band checker

Every computed enclosure produced by `CKFast.exec` is justified with the
already-proved library lemmas of the source certificates (log series
`DyadicFastLog.check_sound`, `ProvedTranscendental.*`, `value_pos_of_accepted_taylor`).
-/

namespace GeneralCK.CKFast
open GeneralCK GeneralCK.Certificates GeneralCK.Certificates.DyadicInterval
open GeneralCK.Certificates.BivariateJetProgram GeneralCK.Certificates.BivariateProvedProgram
open Set

/-! ## Scale facts -/

theorem scale40 : scale 40 = S := by decide
theorem scale64 : scale 64 = 18446744073709551616 := by decide
theorem S_pos : (0 : ℤ) < S := by decide
theorem S24_pos : (0 : ℤ) < S24 := by decide
theorem S_real : ((scale 40 : ℤ) : ℝ) = (S : ℝ) := by rw [scale40]

/-! ## Generic interval facts -/

theorem subsetCheck_self {p : ℕ} (a : DyadicInterval p) : a.subsetCheck a = true := by
  simp [DyadicInterval.subsetCheck]

theorem jet_subsetCheck_self {p : ℕ} (a : DyadicJetEnclosure p) : a.subsetCheck a = true := by
  simp [DyadicJetEnclosure.subsetCheck, subsetCheck_self]

theorem enc_subsetCheck_self {p : ℕ} (a : DyadicBivariateJetEnclosure p) : a.subsetCheck a = true := by
  simp [DyadicBivariateJetEnclosure.subsetCheck, subsetCheck_self]

/-- Lifting a scale-40 interval to scale 64. -/
def lift (a : DI) : DyadicInterval 64 := ⟨a.lo * S24, a.hi * S24⟩

theorem lift_contains {a : DI} {x : ℝ} : (lift a).Contains x ↔ a.Contains x := by
  simp only [DyadicInterval.Contains, lift, Int.cast_mul]
  rw [scale64, scale40]
  simp only [S, S24]
  push_cast
  constructor <;> intro h <;> constructor <;> nlinarith [h.1, h.2]

/-! ## Logarithms -/

theorem ln2E_eq : DyadicLogSeries.enclosure (DyadicFastLog.fraction 64 1 3) nTerms = ln2E := by
  decide +kernel

theorem guard13 : DyadicLogSeries.guard (DyadicFastLog.fraction 64 1 3) = true := by decide +kernel

theorem approx_eq (a b : ℤ) (e : ℕ) :
    approx a b e = DyadicFastLog.approximation 64 a b e nTerms := by
  simp only [approx, DyadicFastLog.approximation, ln2E_eq]

/-- `check` holds for any rounding-outward of `approx`. -/
theorem check_of_guard {a b : ℤ} {e : ℕ} {out : DyadicInterval 64}
    (hg : guardOK a b e = true) (hl : out.lo ≤ (approx a b e).lo) (hh : (approx a b e).hi ≤ out.hi) :
    DyadicFastLog.check a b e nTerms out = true := by
  simp only [guardOK, Bool.and_eq_true, decide_eq_true_eq] at hg
  simp only [DyadicFastLog.check, guard13, hg.2, ← approx_eq, DyadicInterval.subsetCheck,
    Bool.and_eq_true, decide_eq_true_eq, and_true, hl, hh]
  exact hg.1

theorem logPtOK_pos {z : ℤ} (h : logPtOK z = true) : 0 < z := by
  unfold logPtOK guardOK at h
  split_ifs at h with hz
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h; exact h.1.1
  · have : S < z := lt_of_not_ge hz
    exact lt_trans S_pos this

theorem logPt_sound {z : ℤ} (h : logPtOK z = true) :
    (logPt z).Contains (Real.log ((z : ℝ) / (scale 40 : ℝ))) := by
  have hz := logPtOK_pos h
  rw [S_real]
  unfold logPtOK at h
  by_cases hle : z ≤ S
  · rw [if_pos hle] at h
    have hc : DyadicFastLog.check z S (redExp z S) nTerms (lift (logPt z)) = true := by
      apply check_of_guard h
      · simp only [lift, logPt, if_pos hle]; exact floorDiv_mul_le _ S24_pos
      · simp only [lift, logPt, if_pos hle]; exact le_ceilDiv_mul _ S24_pos
    exact lift_contains.mp (DyadicFastLog.check_sound hc)
  · rw [if_neg hle] at h
    have hc : DyadicFastLog.check S z (redExp S z) nTerms (lift (logPt z).neg) = true := by
      apply check_of_guard h
      · simp only [lift, logPt, if_neg hle, DyadicInterval.neg]
        have := le_ceilDiv_mul (-(approx S z (redExp S z)).lo) S24_pos
        linarith
      · simp only [lift, logPt, if_neg hle, DyadicInterval.neg]
        have := floorDiv_mul_le (-(approx S z (redExp S z)).hi) S24_pos
        linarith
    have h1 := lift_contains.mp (DyadicFastLog.check_sound hc)
    have h2 := neg_sound h1
    have hSz : Real.log ((z : ℝ) / (S : ℝ)) = -Real.log ((S : ℝ) / (z : ℝ)) := by
      rw [← Real.log_inv, inv_div]
    rw [hSz]
    have hnn : (logPt z).neg.neg = logPt z := by simp [DyadicInterval.neg]
    rw [← hnn]; exact h2

theorem logIv_sound {b : DI} (h : logIvOK b = true) : ProvedTranscendental.LogEncloses b (logIv b) := by
  simp only [logIvOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hpos, hl⟩, hh⟩ := h
  apply ProvedTranscendental.log_of_endpoints hpos
  · refine DyadicInterval.subsetCheck_sound ?_ (logPt_sound hl)
    simp [DyadicInterval.subsetCheck, logIv]
  · refine DyadicInterval.subsetCheck_sound ?_ (logPt_sound hh)
    simp [DyadicInterval.subsetCheck, logIv]

theorem two_sound (h : logPtOK (2 * S) = true) : two.Contains (Real.log 2) := by
  have := logPt_sound h
  rw [S_real] at this
  have hS : (S : ℝ) ≠ 0 := by norm_num [S]
  simpa [two, hS] using this


/-! ## Reflection contact -/

theorem biasEPt_sound {c : ℤ} (h2 : logPtOK (2 * S) = true) (h : biasEPtOK c = true) :
    (biasEPt c).Contains (Reflection.biasE ((c : ℝ) / (scale 40 : ℝ))) := by
  simp only [biasEPtOK, Bool.and_eq_true] at h
  exact ProvedTranscendental.entropy_encloses (two_sound h2) (logIv_sound h.1) (logIv_sound h.2)
    (subsetCheck_self _) (DyadicContact.point_contains 40 c)

theorem contact_sound {Y c : DI} (h : contactOK Y c = true) :
    ∀ y : ℝ, Y.Contains y → (DyadicContact.enclosure c (contactB c)).Contains reflectionContactJet y := by
  simp only [contactOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hY, hc0⟩, hc1⟩, hco⟩, hbl⟩, hbh⟩, hlo⟩, hhi⟩, h2⟩, hgapLog⟩, hBp⟩, hgap⟩ := h
  have hcS : c.hi ≤ scale 40 := by rw [scale40]; exact hc1
  have hc : ∀ y : ℝ, Y.Contains y → c.Contains (Reflection.biasContact y) := by
    intro y hy
    refine ProvedTranscendental.contact_bracket hc0 hcS hco hY (biasEPt_sound h2 hbl)
      (biasEPt_sound h2 hbh) ?_ ?_ hy
    · simpa [leftOK] using hlo
    · simpa [rightOK] using hhi
  have hB : ∀ x : ℝ, c.Contains x → (contactB c).Contains (Reflection.biasB x) := by
    intro x hx
    exact ProvedTranscendental.denominator_encloses (two_sound h2) (logIv_sound hgapLog)
      (subsetCheck_self _) hx
  intro y hy
  exact ProvedTranscendental.contact_jet hY hc hB hBp hgap (jet_subsetCheck_self _) hy

/-! ## Steps and runs -/

theorem step_valid {h : DI} {s : Shape} {boxes : List Enc} {o : Enc}
    (hs : step h s boxes = some o) : StepValid s boxes o := by
  unfold step at hs
  split_ifs at hs with hr
  cases s with
  | add i j =>
      simp only [Option.some.injEq] at hs; subst hs
      exact ⟨hr, enc_subsetCheck_self _⟩
  | neg i =>
      simp only [Option.some.injEq] at hs; subst hs
      exact ⟨hr, enc_subsetCheck_self _⟩
  | mul i j =>
      simp only [Option.some.injEq] at hs; subst hs
      exact ⟨hr, enc_subsetCheck_self _⟩
  | inv i =>
      simp only at hs
      split_ifs at hs with hp
      simp only [Option.some.injEq] at hs; subst hs
      refine ⟨hr, ?_⟩
      simp only [DyadicBivariateJetEnclosure.invCheck, Bool.and_eq_true]
      exact ⟨hp, enc_subsetCheck_self _⟩
  | log i =>
      simp only at hs
      split_ifs at hs with hl
      simp only [Option.some.injEq] at hs; subst hs
      have hpos : 0 < (boxes.getD i zeroE).value.lo := by
        simp only [logIvOK, Bool.and_eq_true, decide_eq_true_eq] at hl; exact hl.1.1
      exact ⟨hr, hpos, logIv_sound hl, enc_subsetCheck_self _⟩
  | contact i =>
      simp only at hs
      split_ifs at hs with hc
      simp only [Option.some.injEq] at hs; subst hs
      have hpos : 0 < (boxes.getD i zeroE).value.lo := by
        simp only [contactOK, Bool.and_eq_true, decide_eq_true_eq] at hc; exact hc.1.1.1.1.1.1.1.1.1.1.1
      exact ⟨hr, hpos, _, contact_sound hc, enc_subsetCheck_self _⟩

/-- The instruction list realised by a run (proposals = computed enclosures). -/
def prog (h : DI) : List Shape → List Enc → List (BivariateProvedProgram.Instruction 40)
  | [], _ => []
  | s :: rest, boxes =>
      let o := (step h s boxes).getD zeroE
      ⟨s, o⟩ :: prog h rest (o :: boxes)

theorem exec_sound {h : DI} : ∀ {shs : List Shape} {boxes out : List Enc},
    exec h shs boxes = some out →
    Accepted (prog h shs boxes) boxes ∧ finalBoxes (prog h shs boxes) boxes = out ∧
      shapes (prog h shs boxes) = shs
  | [], boxes, out, hx => by
      simp only [exec, Option.some.injEq] at hx; subst hx
      exact ⟨trivial, rfl, rfl⟩
  | s :: rest, boxes, out, hx => by
      simp only [exec] at hx
      cases hst : step h s boxes with
      | none => rw [hst] at hx; exact absurd hx (by simp)
      | some o =>
          rw [hst] at hx
          obtain ⟨ha, hf, hsh⟩ := exec_sound hx
          simp only [prog, hst, Option.getD_some]
          exact ⟨⟨step_valid hst, ha⟩, hf, by simpa [shapes] using hsh⟩


/-! ## Input registers -/

theorem D_pos : (0 : ℤ) < D := by decide

theorem ivZ_contains {n0 n1 d : ℤ} (hd : 0 < d) {x : ℝ} (h0 : (n0 : ℝ) / d ≤ x) (h1 : x ≤ (n1 : ℝ) / d) :
    (ivZ n0 n1 d).Contains x := by
  have hSp : (0 : ℝ) < (S : ℝ) := by norm_num [S]
  have hdr : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hf : ((floorDiv (n0 * S) d : ℤ) : ℝ) * d ≤ (n0 : ℝ) * S := by
    exact_mod_cast floorDiv_mul_le (n0 * S) hd
  have hc : (n1 : ℝ) * S ≤ ((ceilDiv (n1 * S) d : ℤ) : ℝ) * d := by
    exact_mod_cast le_ceilDiv_mul (n1 * S) hd
  rw [div_le_iff₀ hdr] at h0
  rw [le_div_iff₀ hdr] at h1
  simp only [DyadicInterval.Contains, ivZ, S_real]
  constructor
  · by_contra hlt
    rw [not_le] at hlt
    have := mul_lt_mul_of_pos_right hlt hdr
    nlinarith [mul_le_mul_of_nonneg_left h0 hSp.le]
  · by_contra hlt
    rw [not_le] at hlt
    have := mul_lt_mul_of_pos_right hlt hdr
    nlinarith [mul_le_mul_of_nonneg_left h1 hSp.le]

theorem inputJets_eq (ac zc a z : ℝ) : CorrectionFactorizedProgramKernel.inputJets ac zc a z =
    [BivariateJet2.coordinateA (Jet2.segment ac a).value, BivariateJet2.coordinateZ (Jet2.segment zc z).value,
      BivariateJet2.const ((1 : ℤ) : ℝ), BivariateJet2.const ((2 : ℤ) : ℝ)] := by
  simp only [CorrectionFactorizedProgramKernel.inputJets, Int.cast_one, Int.cast_ofNat]
  rfl

theorem initial_contains {a z : DI} {ac zc x y t : ℝ}
    (hA : a.Contains ((Jet2.segment ac x).value t))
    (hZ : z.Contains ((Jet2.segment zc y).value t)) :
    RegistersContain (initial a z)
      (CorrectionFactorizedProgramKernel.inputJets ac zc x y) t := by
  rw [inputJets_eq]
  exact ((((RegistersContain.nil 40 t).cons (DyadicBivariateJetEnclosure.contains_const 40 2 t)).cons
      (DyadicBivariateJetEnclosure.contains_const 40 1 t)).cons
      (DyadicBivariateJetEnclosure.contains_coordinateZ hZ)).cons
      (DyadicBivariateJetEnclosure.contains_coordinateA hA)

theorem segment_mem {n0 n1 d : ℤ} (hd : 0 < d) {c x t : ℝ}
    (hc : c ∈ Icc ((n0 : ℝ) / d) ((n1 : ℝ) / d)) (hx : x ∈ Icc ((n0 : ℝ) / d) ((n1 : ℝ) / d))
    (ht : t ∈ Icc (0 : ℝ) 1) : (ivZ n0 n1 d).Contains ((Jet2.segment c x).value t) :=
  DyadicInterval.contains_segment (ivZ_contains hd hc.1 hc.2) (ivZ_contains hd hx.1 hx.2) ht

theorem initial_sound (ac zc a z : ℝ) : ∀ i,
    ((CorrectionFactorizedProgramKernel.inputJets ac zc a z).getD i zeroJet).DirectionalSoundOn
      (a - ac) (z - zc) (Icc (0 : ℝ) 1) := by
  intro i t ht
  have hconst (c : ℝ) : (BivariateJet2.const c).DirectionalSoundAt (a - ac) (z - zc) t := by
    simpa only [BivariateJet2.DirectionalSoundAt, BivariateJet2.projection_const] using
      Jet2.soundAt_const c t
  have h : RegistersSound (CorrectionFactorizedProgramKernel.inputJets ac zc a z) (a - ac) (z - zc) t :=
    ((((RegistersSound.nil _ _ t).cons (hconst 2)).cons (hconst 1)).cons
      (BivariateJet2.soundOn_affineZ zc z (a - ac) _ t ht)).cons
      (BivariateJet2.soundOn_affineA ac a (z - zc) _ t ht)
  exact h i

/-! ## Taylor bound -/

theorem mag_real (i : DI) : ((mag i : ℤ) : ℝ) / (S : ℝ) = JetBounds.Interval.magnitude i.toReal := by
  have hS : (0 : ℝ) < ((scale 40 : ℤ) : ℝ) := by rw [scale40]; norm_num [S]
  simp only [mag, JetBounds.Interval.magnitude, DyadicInterval.toReal, abs_div, abs_of_pos hS]
  rw [max_div_div_right hS.le, scale40]
  push_cast; rfl

theorem taylorZ_real (c w : Enc) (A Z : ℤ) :
    ((taylorZ c w A Z : ℤ) : ℝ) = 8 * (D : ℝ) ^ 2 * (S : ℝ) *
      BivariateJetEnclosure.taylorLower c.toReal w.toReal ((A : ℝ) / (2 * D)) ((Z : ℝ) / (2 * D)) := by
  have hD : (D : ℝ) ≠ 0 := by norm_num [D]
  have hS : (S : ℝ) ≠ 0 := by norm_num [S]
  simp only [BivariateJetEnclosure.taylorLower, DyadicBivariateJetEnclosure.toReal, ← mag_real]
  simp only [DyadicInterval.toReal, S_real, taylorZ]
  push_cast
  field_simp
  ring

theorem taylor_pos {c w : Enc} {A Z : ℤ} (h : 0 < taylorZ c w A Z) :
    0 < BivariateJetEnclosure.taylorLower c.toReal w.toReal ((A : ℝ) / (2 * D)) ((Z : ℝ) / (2 * D)) := by
  have h' : (0 : ℝ) < ((taylorZ c w A Z : ℤ) : ℝ) := by exact_mod_cast h
  rw [taylorZ_real] at h'
  have hk : (0 : ℝ) < 8 * (D : ℝ) ^ 2 * (S : ℝ) := by norm_num [D, S]
  exact pos_of_mul_pos_right h' hk.le

theorem ckShapes_eq : ckShapes = shapes CorrectionFactorizedProgramKernel.kernelProgram := by
  decide +kernel

/-! ## One cell -/

theorem cell_sound {U0 U1 R0 R1 : ℤ} {h : Hint} (hok : cellOK U0 U1 R0 R1 h = true)
    {u rho : ℝ} (hu : u ∈ Icc ((U0 : ℝ) / D) ((U1 : ℝ) / D))
    (hr : rho ∈ Icc ((R0 : ℝ) / D) ((R1 : ℝ) / D)) (hr1 : rho < 1) :
    0 < Correction.Mleft (H u) (H (u + rho * (1/2 - u))) ∧
    0 < Correction.Mdet (H u) (H (u + rho * (1/2 - u))) := by
  simp only [cellOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨hu0, hu01⟩, hu1⟩, hr0⟩, hr01⟩, hrun⟩ := hok
  cases hce : exec h.hc ckShapes (centerRegs U0 U1 R0 R1) with
  | none => rw [hce] at hrun; simp at hrun
  | some ce =>
  cases hwh : exec h.hw ckShapes (wholeRegs U0 U1 R0 R1) with
  | none => rw [hce, hwh] at hrun; simp at hrun
  | some wh =>
  rw [hce, hwh] at hrun
  simp only [taylorOK, Bool.and_eq_true, decide_eq_true_eq] at hrun
  obtain ⟨hA, hsA, hshA⟩ := exec_sound hce
  obtain ⟨hB, hsB, hshB⟩ := exec_sound hwh
  have hDr : (0 : ℝ) < (D : ℝ) := by norm_num [D]
  have hD2 : (0 : ℤ) < 2 * D := by decide
  have hU : (U0 : ℝ) ≤ U1 := by exact_mod_cast hu01
  have hR : (R0 : ℝ) ≤ R1 := by exact_mod_cast hr01
  set ac : ℝ := ((U0 + U1 : ℤ) : ℝ) / ((2 * D : ℤ) : ℝ)
  set zc : ℝ := ((R0 + R1 : ℤ) : ℝ) / ((2 * D : ℤ) : ℝ)
  have hac : ac = ((U0 : ℝ) / D + (U1 : ℝ) / D) / 2 := by simp only [ac]; push_cast; field_simp
  have hzc : zc = ((R0 : ℝ) / D + (R1 : ℝ) / D) / 2 := by simp only [zc]; push_cast; field_simp
  have hUd : (U0 : ℝ) / D ≤ (U1 : ℝ) / D := div_le_div_of_nonneg_right hU hDr.le
  have hRd : (R0 : ℝ) / D ≤ (R1 : ℝ) / D := div_le_div_of_nonneg_right hR hDr.le
  have hacm : ac ∈ Icc ((U0 : ℝ) / D) ((U1 : ℝ) / D) := by rw [hac]; constructor <;> linarith
  have hzcm : zc ∈ Icc ((R0 : ℝ) / D) ((R1 : ℝ) / D) := by rw [hzc]; constructor <;> linarith
  have hcreg : RegistersContain (centerRegs U0 U1 R0 R1)
      (CorrectionFactorizedProgramKernel.inputJets ac zc u rho) 0 := by
    apply initial_contains
    · simp only [Jet2.segment, zero_mul, add_zero]
      exact ivZ_contains hD2 le_rfl le_rfl
    · simp only [Jet2.segment, zero_mul, add_zero]
      exact ivZ_contains hD2 le_rfl le_rfl
  have hwreg : ∀ t ∈ Icc (0 : ℝ) 1, RegistersContain (wholeRegs U0 U1 R0 R1)
      (CorrectionFactorizedProgramKernel.inputJets ac zc u rho) t :=
    fun t ht => initial_contains (segment_mem D_pos hacm hu ht) (segment_mem D_pos hzcm hr ht)
  have hra : (0 : ℝ) ≤ ((U1 - U0 : ℤ) : ℝ) / (2 * D) := by push_cast; apply div_nonneg <;> linarith
  have hrz : (0 : ℝ) ≤ ((R1 - R0 : ℤ) : ℝ) / (2 * D) := by push_cast; apply div_nonneg <;> linarith
  have hda : |u - ac| ≤ ((U1 - U0 : ℤ) : ℝ) / (2 * D) := by
    rw [hac, abs_le]; push_cast
    have e : ((U1 : ℝ) - U0) / (2 * D) = ((U1 : ℝ) / D - (U0 : ℝ) / D) / 2 := by field_simp
    rw [e]; constructor <;> linarith [hu.1, hu.2]
  have hdz : |rho - zc| ≤ ((R1 - R0 : ℤ) : ℝ) / (2 * D) := by
    rw [hzc, abs_le]; push_cast
    have e : ((R1 : ℝ) - R0) / (2 * D) = ((R1 : ℝ) / D - (R0 : ℝ) / D) / 2 := by field_simp
    rw [e]; constructor <;> linarith [hr.1, hr.2]
  have hshape : shapes (prog h.hc ckShapes (centerRegs U0 U1 R0 R1)) =
      shapes (prog h.hw ckShapes (wholeRegs U0 U1 R0 R1)) := by rw [hshA, hshB]
  have hkern : shapes (prog h.hw ckShapes (wholeRegs U0 U1 R0 R1)) =
      shapes CorrectionFactorizedProgramKernel.kernelProgram := by rw [hshB, ckShapes_eq]
  have pos (i : ℕ) (hi : 0 < taylorZ (ce.getD i zeroE) (wh.getD i zeroE) (U1 - U0) (R1 - R0)) :
      0 < ((finalJets (prog h.hw ckShapes (wholeRegs U0 U1 R0 R1))
        (CorrectionFactorizedProgramKernel.inputJets ac zc u rho)).getD i zeroJet).value 1 := by
    refine value_pos_of_accepted_taylor _ _ i hshape hcreg hwreg (initial_sound _ _ u rho) hA hB
      hra hrz hda hdz ?_
    rw [hsA, hsB]
    exact taylor_pos hi
  have hm := pos 14 hrun.1
  have hk := pos 0 hrun.2
  rw [CorrectionFactorizedProgramKernel.output_value_m11_of_shapes _ hkern] at hm
  rw [CorrectionFactorizedProgramKernel.output_value_kdet_of_shapes _ hkern] at hk
  simp only [one_mul, add_sub_cancel] at hm hk
  have hu0r : (0 : ℝ) < u := lt_of_lt_of_le (div_pos (by exact_mod_cast hu0) hDr) hu.1
  have hgap : (0 : ℝ) < 1/2 - u := by
    have h' : (2 : ℝ) * U1 < D := by exact_mod_cast hu1
    have : (U1 : ℝ) / D < 1/2 := by rw [div_lt_iff₀ hDr]; linarith
    linarith [hu.2]
  have hr0r : (0 : ℝ) < rho := lt_of_lt_of_le (div_pos (by exact_mod_cast hr0) hDr) hr.1
  have heq := Correction.Natural.kernel_eq_actual_ratio hu0r hgap hr0r hr1
  rw [heq.1] at hm
  rw [heq.2] at hk
  set w := u + rho * (1/2 - u)
  have huw : u < w := by simp only [w]; nlinarith [mul_pos hr0r hgap]
  have hw : w < 1/2 := by simp only [w]; nlinarith [mul_pos (show (0:ℝ) < 1 - rho by linarith) hgap]
  have hf0 := H_pos (hu0r.trans huw) (show w < 1 by linarith)
  have hf1 : H w < 1 := by
    have h' := H_strictMonoOn ⟨(hu0r.trans huw).le, hw.le⟩ (by norm_num : (1/2 : ℝ) ∈ Icc 0 (1/2)) hw
    simpa only [H_half] using h'
  exact ⟨hm, (Correction.Mdet_pos_iff_Kfactored_pos hf0 hf1).mpr hk⟩

/-! ## Covers -/

theorem tree_sound : ∀ {U0 U1 R0 R1 : ℤ} {t : Tree}, treeOK U0 U1 R0 R1 t = true →
    ∀ (u rho : ℝ), u ∈ Icc ((U0 : ℝ) / D) ((U1 : ℝ) / D) → rho ∈ Icc ((R0 : ℝ) / D) ((R1 : ℝ) / D) →
    rho < 1 →
    0 < Correction.Mleft (H u) (H (u + rho * (1/2 - u))) ∧
    0 < Correction.Mdet (H u) (H (u + rho * (1/2 - u)))
  | _, _, _, _, .leaf h, ht => fun _ _ hu hr hr1 => cell_sound ht hu hr hr1
  | U0, U1, R0, R1, .su m l r, ht => by
      simp only [treeOK, Bool.and_eq_true, decide_eq_true_eq] at ht
      obtain ⟨⟨⟨_, _⟩, hl⟩, hrr⟩ := ht
      intro u rho hu hr hr1
      by_cases hm : u ≤ (m : ℝ) / D
      · exact tree_sound hl u rho ⟨hu.1, hm⟩ hr hr1
      · exact tree_sound hrr u rho ⟨le_of_lt (lt_of_not_ge hm), hu.2⟩ hr hr1
  | U0, U1, R0, R1, .sr m l r, ht => by
      simp only [treeOK, Bool.and_eq_true, decide_eq_true_eq] at ht
      obtain ⟨⟨⟨_, _⟩, hl⟩, hrr⟩ := ht
      intro u rho hu hr hr1
      by_cases hm : rho ≤ (m : ℝ) / D
      · exact tree_sound hl u rho hu ⟨hr.1, hm⟩ hr1
      · exact tree_sound hrr u rho hu ⟨le_of_lt (lt_of_not_ge hm), hr.2⟩ hr1

end GeneralCK.CKFast


theorem solution {U0 U1 R0 R1 : ℤ} {t : GeneralCK.CKFast.Tree}
    (ht : GeneralCK.CKFast.treeOK U0 U1 R0 R1 t = true) (u rho : ℝ)
    (hu : u ∈ Set.Icc ((U0 : ℝ) / GeneralCK.CKFast.D) ((U1 : ℝ) / GeneralCK.CKFast.D))
    (hr : rho ∈ Set.Icc ((R0 : ℝ) / GeneralCK.CKFast.D) ((R1 : ℝ) / GeneralCK.CKFast.D))
    (hr1 : rho < 1) :
    0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
    0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) :=
  GeneralCK.CKFast.tree_sound ht u rho hu hr hr1
