-- Prove2me | solution 1 for OAI.SourcePatternTail.uniform
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T14:56:26.887359+00:00
-- url     : https://prove2.me/submissions/cc190976-1f69-4dfe-ba2a-4c5029034224

import Mathlib
import Definitions.Def_OAIQ16Cd000
import Definitions.Def_OAIQ16Cd001
import Theorems.Thm_OAI_PatternTail_bound

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_RadialShell
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace RadialShell
open Filter
open scoped Topology

lemma inv_limit : Tendsto (fun n : ℕ => (n:ℝ)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
lemma eta_limit : Tendsto η atTop (𝓝 0) := by
  unfold η
  simpa only [zero_pow (by norm_num : (4:ℕ) ≠ 0)] using inv_limit.pow 4
lemma log_div_limit : Tendsto (fun n : ℕ => Real.log n/(n:ℝ)) atTop (𝓝 0) := by
  have ht : Tendsto (fun x : ℝ => Real.log x/x) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  exact ht.comp tendsto_natCast_atTop_atTop
lemma low_limit (a : ℝ) : Tendsto (low a) atTop (𝓝 a) := by
  unfold low
  simpa using (((tendsto_const_nhds (x := (1:ℝ))).sub (log_div_limit.const_mul 10)).const_mul a).sub (eta_limit.const_mul 3)
lemma high_limit (a : ℝ) : Tendsto (high a) atTop (𝓝 a) := by
  unfold high
  simpa using (((tendsto_const_nhds (x := (1:ℝ))).add inv_limit).const_mul a).add (eta_limit.const_mul 3)

end RadialShell

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_CoveringGrowth
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace CoveringGrowth
open Filter Real
open scoped Topology

lemma polynomial {C δ : ℝ} (hδ : 0 < δ) (k : ℕ) :
    ∀ᶠ n : ℕ in atTop,C*(n:ℝ)^k ≤ Real.exp (δ*(n:ℝ)) := by
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (k:ℝ) δ hδ).comp
    tendsto_natCast_atTop_atTop
  have ht' : Tendsto (fun n : ℕ => C*((n:ℝ)^k*Real.exp (-δ*(n:ℝ)))) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.rpow_natCast,mul_zero] using ht.const_mul C
  filter_upwards [ht'.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))] with n hn
  have he := mul_le_mul_of_nonneg_right hn.le (Real.exp_pos (δ*(n:ℝ))).le
  have hid : Real.exp (-δ*(n:ℝ))*Real.exp (δ*(n:ℝ)) = 1 := by rw [← Real.exp_add]; convert Real.exp_zero using 2 ; ring
  calc
    _ = (C*((n:ℝ)^k*Real.exp (-δ*(n:ℝ))))*Real.exp (δ*(n:ℝ)) := by rw [mul_assoc,mul_assoc,hid,mul_one]
    _ ≤ _ := by simpa only [one_mul] using he

lemma moving_base {b : ℕ → ℝ} {B rate : ℝ} (hB : 0 < B)
    (hb : Tendsto b atTop (𝓝 B)) (hrate : Real.log B < rate) :
    ∀ᶠ n : ℕ in atTop,0 < b n ∧ (b n)^n ≤ Real.exp (rate*(n:ℝ)) := by
  have ht : Tendsto (fun n => Real.log (b n)) atTop (𝓝 (Real.log B)) :=
    (Real.continuousAt_log hB.ne').tendsto.comp hb
  filter_upwards [hb.eventually (lt_mem_nhds hB),ht.eventually (gt_mem_nhds hrate)] with n hn hlog
  refine ⟨hn,?_⟩
  calc
    _ = Real.exp ((n:ℝ)*Real.log (b n)) := by rw [Real.exp_nat_mul,Real.exp_log hn]
    _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hlog.le (Nat.cast_nonneg n) |>.trans_eq (mul_comm _ _))

lemma combined {b : ℕ → ℝ} {B C rate : ℝ} (hB : 0 < B)
    (hb : Tendsto b atTop (𝓝 B)) (hrate : Real.log B < rate) (_hC : 0 ≤ C) (k : ℕ) :
    ∀ᶠ n : ℕ in atTop,C*(n:ℝ)^k*(b n)^n ≤ Real.exp (rate*(n:ℝ)) := by
  let rate₁ := (Real.log B+rate)/2
  have h₁ : Real.log B < rate₁ := by dsimp [rate₁]; linarith
  have h₂ : 0 < rate-rate₁ := by dsimp [rate₁]; linarith
  filter_upwards [moving_base hB hb h₁,polynomial (C := C) h₂ k] with n hn hp
  have hm := mul_le_mul hp hn.2 (pow_nonneg hn.1.le _) (Real.exp_pos ((rate-rate₁)*(n:ℝ))).le
  apply hm.trans_eq
  rw [← Real.exp_add]
  congr 1
  ring

end CoveringGrowth

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_SourceParameters
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace SourceParameters
open Filter
open scoped Topology
lemma a_pos : 0 < a := by norm_num [a,ε]
lemma a_one : 1 < a := by norm_num [a,ε]
lemma D_pos : 0 < D := by norm_num [D]
lemma L_limit : Tendsto L atTop (𝓝 (D+a)) := by
  unfold L b
  convert (tendsto_const_nhds (x := D)).add
    (((tendsto_const_nhds (x := (1:ℝ))).add RadialShell.inv_limit).const_mul a) |>.add
      (RadialShell.eta_limit.const_mul 5) using 1 ; simp
lemma base_limit : Tendsto (fun n => L n/a) atTop (𝓝 ((D+a)/a)) :=
  L_limit.div_const a
lemma base_log : Real.log ((D+a)/a) < 1/200 := by
  have hp : 0 < (D+a)/a := div_pos (add_pos D_pos a_pos) a_pos
  have hh := Real.log_le_sub_one_of_pos hp
  have he : (D+a)/a-1 < (1:ℝ)/200 := by norm_num [D,a,ε]
  exact hh.trans_lt he
lemma length_rate : ∀ᶠ n : ℕ in atTop,∀ R : ℝ,0 ≤ R → R ≤ (n:ℝ)^2 →
    (N n R:ℝ) ≤ Real.exp ((1/100:ℝ)*(n:ℝ)) := by
  have ha := a_pos
  have hv : 0 < v := by norm_num [v]
  have hb : 0 < (D+a)/a := div_pos (add_pos D_pos a_pos) a_pos
  have hx := CoveringGrowth.combined (C := 1281) hb base_limit
    (base_log.trans (by norm_num : (1:ℝ)/200<1/100)) (by norm_num) 2
  filter_upwards [hx,eventually_ge_atTop 1] with n hn hn1 R hR hRn
  have hnp : (1:ℝ) ≤ n := by exact_mod_cast hn1
  have hbase : 1 ≤ L n/a := by
    apply (le_div_iff₀ a_pos).mpr
    have hh : 0 ≤ a*(n:ℝ)⁻¹ := by positivity
    have heta : 0 ≤ RadialShell.η n := by unfold RadialShell.η; positivity
    dsimp [L,b]
    nlinarith only [D_pos,hh,heta]
  have hp : 1 ≤ (L n/a)^n := one_le_pow₀ hbase
  have hceil : (N n R:ℝ) ≤ 20*R/v*(L n/a)^n+1 := by
    exact (Nat.ceil_lt_add_one (by positivity : 0 ≤ 20*R/v*(L n/a)^n)).le
  calc
    _ ≤ 20*R/v*(L n/a)^n+1 := hceil
    _ ≤ 1280*(n:ℝ)^2*(L n/a)^n+1 := by
      have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hRn (by norm_num : (0:ℝ)≤1280)) (le_trans (by norm_num) hp)
      norm_num [v] at *
      linarith only [hh]
    _ ≤ 1281*(n:ℝ)^2*(L n/a)^n := by
      have hn2 : 1 ≤ (n:ℝ)^2 := one_le_pow₀ hnp
      have hh := mul_le_mul hn2 hp (by norm_num : (0:ℝ)≤1) (sq_nonneg (n:ℝ))
      nlinarith only [hh]
    _ ≤ _ := hn
lemma coarse_base : ∀ᶠ n : ℕ in atTop,
    0 < RadialShell.high a n*(4*Real.sqrt ε)/D ∧
    (RadialShell.high a n*(4*Real.sqrt ε)/D)^n ≤ Real.exp (-(n:ℝ)) := by
  have hε : Real.sqrt ε = 1/32768 := by
    norm_num [ε,Real.sqrt_div,Real.sqrt_eq_iff_mul_self_eq]
  have hB : 0 < a*(4*Real.sqrt ε)/D := by rw [hε]; norm_num [a,ε,D]
  have hb := (RadialShell.high_limit a).mul_const (4*Real.sqrt ε) |>.div_const D
  have hr : Real.log (a*(4*Real.sqrt ε)/D) < -1 := by
    apply Real.log_lt_iff_lt_exp hB |>.mpr
    rw [hε]
    exact (by norm_num [a,ε,D] : a*(4*(1/32768))/D < (0.36787944116:ℝ)).trans Real.exp_neg_one_gt_d9
  simpa only [neg_one_mul] using CoveringGrowth.moving_base hB hb hr
end SourceParameters

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_CoveringAsymptotics
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace CoveringGrowth
open Filter Real
open scoped Topology
lemma super_domination {C δ r : ℝ} (hδ : 0 < δ) (k : ℕ) :
    ∀ᶠ n : ℕ in atTop,C*(n:ℝ)^k*Real.exp (r*(n:ℝ)) ≤
      Real.exp (δ*((n:ℝ)*Real.log n)) := by
  filter_upwards [polynomial (C := C) (by norm_num : (0:ℝ)<1) k,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop ((r+1)/δ))] with n hn hl
  calc
    _ ≤ Real.exp (n:ℝ)*Real.exp (r*(n:ℝ)) := by gcongr; simpa using hn
    _ = Real.exp ((r+1)*(n:ℝ)) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (by
      change (r+1)/δ ≤ Real.log n at hl
      have hh := mul_le_mul_of_nonneg_right ((div_le_iff₀ hδ).mp hl) (Nat.cast_nonneg (α := ℝ) n)
      nlinarith only [hh])

lemma exponential_domination {C δ r : ℝ} (hδ : 0 < δ) (k : ℕ) :
    ∀ᶠ n : ℕ in atTop,C*(n:ℝ)^k*Real.exp (-δ*((n:ℝ)*Real.log n)) ≤
      Real.exp (r*(n:ℝ)) := by
  filter_upwards [super_domination (C := C) (r := -r) hδ k] with n hn
  have hh := mul_le_mul_of_nonneg_right hn
    (Real.exp_pos (-δ*((n:ℝ)*Real.log n)+r*(n:ℝ))).le
  have he₁ : C*(n:ℝ)^k*Real.exp (-r*(n:ℝ))*Real.exp (-δ*((n:ℝ)*Real.log n)+r*(n:ℝ)) =
      C*(n:ℝ)^k*Real.exp (-δ*((n:ℝ)*Real.log n)) := by
    rw [mul_assoc,← Real.exp_add]
    congr 2
    ring
  have he₂ : Real.exp (δ*((n:ℝ)*Real.log n))*Real.exp (-δ*((n:ℝ)*Real.log n)+r*(n:ℝ)) = Real.exp (r*(n:ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rwa [he₁,he₂] at hh

lemma fine_base {C : ℝ} (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop,C*Real.sqrt (Real.log n/(n:ℝ)) ≤
      Real.exp (-(1/3:ℝ)*Real.log n) := by
  have he := (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/3)).bound
    (show 0 < 1/C^2 by positivity)
  have he' := tendsto_natCast_atTop_atTop.eventually he
  filter_upwards [he',eventually_ge_atTop 2] with n hn hn2
  have hnp : (0:ℝ) < n := by exact_mod_cast (by omega : 0<n)
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1≤n))
  simp only [Real.norm_eq_abs,abs_of_nonneg hlog,
    abs_of_nonneg (Real.rpow_nonneg hnp.le _)] at hn
  apply (sq_le_sq₀ (by positivity) (Real.exp_pos _).le).mp
  rw [mul_pow,Real.sq_sqrt (div_nonneg hlog hnp.le),← Real.exp_nat_mul]
  have hh := mul_le_mul_of_nonneg_left hn (sq_nonneg C)
  have hc : C^2*((1/C^2)*(n:ℝ)^(1/3:ℝ)) = (n:ℝ)^(1/3:ℝ) := by field_simp
  rw [hc,Real.rpow_def_of_pos hnp] at hh
  have hdiv := (div_le_div_of_nonneg_right hh hnp.le)
  have hid : Real.exp (Real.log n*(1/3:ℝ))/(n:ℝ) =
      Real.exp ((2:ℝ)*(-(1/3:ℝ)*Real.log n)) := by
    conv_lhs => rw [← Real.exp_log hnp]
    rw [← Real.exp_sub,Real.log_exp]
    congr 1
    ring
  rw [hid] at hdiv
  simpa only [mul_div_assoc,Nat.cast_ofNat] using hdiv
end CoveringGrowth

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_NumericTail
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace NumericTail
open Filter Real SourceParameters
open scoped Topology
lemma target_count {n : ℕ} (hn : 1 ≤ n) :
    Real.exp ((n:ℝ)*Real.log n/16) ≤ (M n:ℝ) ∧
    (M n:ℝ) ≤ 2*Real.exp ((n:ℝ)*Real.log n/16) := by
  have hl : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have he : 1 ≤ Real.exp ((n:ℝ)*Real.log n/16) := Real.one_le_exp_iff.mpr (by positivity)
  exact ⟨Nat.le_ceil _,(Nat.ceil_lt_add_one (Real.exp_pos _).le).le.trans (by linarith only [he])⟩

lemma fine_small {H : ℝ} (hH : 0 < H) : ∀ᶠ n : ℕ in atTop,
    ∀ S : ℝ,0 ≤ S → S ≤ Real.exp ((1/100:ℝ)*(n:ℝ)) →
    (M n:ℝ)^2*(12*((n:ℝ)+1)*S^2*
      (RadialShell.high a n*(H*Real.sqrt (Real.log n/(n:ℝ)))/D)^(n-1)) < 1/2 := by
  have hDp := D_pos
  have hC : 0 < 2*H/D := by positivity
  have hh := CoveringGrowth.fine_base hC
  have hd := CoveringGrowth.exponential_domination (C := 96) (δ := 1/6) (r := -2) (by norm_num) 1
  filter_upwards [hh,hd,(RadialShell.high_limit a).eventually_le_const
    (by norm_num [a,ε] : a<2),eventually_ge_atTop 8] with n hf hd hu hn S hS hSb
  have hn1 : 1 ≤ n := by omega
  have hnp : (1:ℝ) ≤ n := by exact_mod_cast hn1
  have hn8 : (8:ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1<n))
  have hhi : 0 ≤ RadialShell.high a n := by unfold RadialShell.high RadialShell.η; have := a_pos; positivity
  have hbase : RadialShell.high a n*(H*Real.sqrt (Real.log n/(n:ℝ)))/D ≤
      Real.exp (-(1/3:ℝ)*Real.log n) := by
    apply le_trans _ hf
    have hh := mul_le_mul_of_nonneg_right hu (by positivity : 0 ≤ H*Real.sqrt (Real.log n/(n:ℝ)))
    apply (div_le_div_of_nonneg_right hh D_pos.le).trans_eq
    ring
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ RadialShell.high a n*(H*Real.sqrt (Real.log n/(n:ℝ)))/D) hbase (n-1)
  rw [← Real.exp_nat_mul] at hp
  have hm := pow_le_pow_left₀ (Nat.cast_nonneg (M n)) (target_count hn1).2 2
  rw [mul_pow,← Real.exp_nat_mul] at hm
  have hs := pow_le_pow_left₀ hS hSb 2
  rw [← Real.exp_nat_mul] at hs
  have hnn : (n:ℝ)+1 ≤ 2*(n:ℝ) := by linarith only [hnp]
  calc
    _ ≤ (2:ℝ)^2*Real.exp ((2:ℕ)*((n:ℝ)*Real.log n/16))*
      (12*(2*(n:ℝ))*Real.exp ((2:ℕ)*((1/100:ℝ)*(n:ℝ)))*
        Real.exp (((n-1:ℕ):ℝ)*(-(1/3:ℝ)*Real.log n))) := by gcongr
    _ = 96*(n:ℝ)*Real.exp ((1/50:ℝ)*(n:ℝ))*
      Real.exp (((n:ℝ)/8-((n:ℝ)-1)/3)*Real.log n) := by
        rw [Nat.cast_sub hn1]
        norm_num only [Nat.cast_ofNat,Nat.cast_one]
        calc
          _ = 96*(n:ℝ)*(Real.exp (2*((n:ℝ)*Real.log n/16))*
            Real.exp (2*((1/100:ℝ)*(n:ℝ)))*Real.exp (((n:ℝ)-1)*(-(1/3:ℝ)*Real.log n))) := by ring
          _ = _ := by
            simp only [← Real.exp_add,mul_assoc]
            congr 2
            ring_nf
    _ ≤ 96*(n:ℝ)*Real.exp ((1/50:ℝ)*(n:ℝ))*
      Real.exp (-(1/6:ℝ)*((n:ℝ)*Real.log n)) := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
        nlinarith only [mul_nonneg (by linarith only [hn8] : 0 ≤ (n:ℝ)-8) hlog.le]
    _ = (96*(n:ℝ)^1*Real.exp (-(1/6:ℝ)*((n:ℝ)*Real.log n)))*
      Real.exp ((1/50:ℝ)*(n:ℝ)) := by ring
    _ ≤ Real.exp (-2*(n:ℝ))*Real.exp ((1/50:ℝ)*(n:ℝ)) := by gcongr
    _ ≤ Real.exp (-1) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      linarith only [hnp]
    _ < 1/2 := Real.exp_neg_one_lt_half
end NumericTail

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_TailComparison
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace NumericTail
open Filter Real SourceParameters
open scoped Topology
lemma coarse_shift {n : ℕ} (hn : 1 ≤ n)
    (hb : (RadialShell.high a n*(4*Real.sqrt ε)/D)^n ≤ Real.exp (-(n:ℝ))) :
    (RadialShell.high a n*(4*Real.sqrt ε)/D)^(n-1) ≤ 16*Real.exp (-(n:ℝ)) := by
  have he : Real.sqrt ε = 1/32768 := by norm_num [ε,Real.sqrt_div,Real.sqrt_eq_iff_mul_self_eq]
  have hbase : (1:ℝ)/16 ≤ RadialShell.high a n*(4*Real.sqrt ε)/D := by
    rw [he]
    have ha := a_one
    have hη : 0 ≤ RadialShell.η n := by unfold RadialShell.η; positivity
    have hi : 0 ≤ a*(n:ℝ)⁻¹ := mul_nonneg a_pos.le (inv_nonneg.mpr (Nat.cast_nonneg _))
    dsimp [RadialShell.high,D]
    nlinarith only [ha,hη,hi]
  have hp := pow_nonneg (le_trans (by norm_num) hbase) (n-1)
  have hm := mul_le_mul_of_nonneg_left hbase hp
  rw [← pow_succ, Nat.sub_add_cancel hn] at hm
  linarith only [hm,hb]

lemma activity_decay {B : ℝ} (hB : 0 < B) : ∀ᶠ n : ℕ in atTop,
    ∀ Q F : ℝ,0 ≤ Q → Q ≤ B*(n:ℝ)^2 → F ≤ (n:ℝ)*Real.log n/64 →
      8*Q*Real.exp F/(M n:ℝ) ≤ Real.exp (-(3/4:ℝ)*(n:ℝ)) := by
  filter_upwards [CoveringGrowth.exponential_domination (C := 8*B) (δ := 3/64)
    (r := -(3/4)) (by norm_num) 2,eventually_ge_atTop 1] with n hn hn1 Q F hQ hQB hF
  have hm := (target_count hn1).1
  have hMp : 0 < (M n:ℝ) := (Real.exp_pos _).trans_le hm
  calc
    _ ≤ 8*(B*(n:ℝ)^2)*Real.exp ((n:ℝ)*Real.log n/64)/Real.exp ((n:ℝ)*Real.log n/16) := by gcongr
    _ = (8*B)*(n:ℝ)^2*Real.exp (-(3/64:ℝ)*((n:ℝ)*Real.log n)) := by
      rw [mul_div_assoc,← Real.exp_sub]
      congr 1 <;> ring_nf
    _ ≤ _ := hn

lemma coarse_decay {B : ℝ} (hB : 0 < B) : ∀ᶠ n : ℕ in atTop,
    ∀ S Q : ℝ,0 ≤ S → S ≤ Real.exp ((1/100:ℝ)*(n:ℝ)) →
      0 ≤ Q → Q ≤ B*(n:ℝ)^2 →
      80*(n:ℝ)⁻¹^3*Q^2*(12*((n:ℝ)+1)*S^2*
        (RadialShell.high a n*(4*Real.sqrt ε)/D)^(n-1)) ≤
      Real.exp (-(3/4:ℝ)*(n:ℝ)) := by
  filter_upwards [SourceParameters.coarse_base,
    CoveringGrowth.polynomial (C := 30720*B^2) (δ := 23/100) (by norm_num) 5,
    eventually_ge_atTop 1] with n hb hn hn1 S Q hS hSb hQ hQb
  have hnp : (1:ℝ) ≤ n := by exact_mod_cast hn1
  have hi : (n:ℝ)⁻¹^3 ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hnp)
  have hs := pow_le_pow_left₀ hS hSb 2
  rw [← Real.exp_nat_mul] at hs
  have hq := pow_le_pow_left₀ hQ hQb 2
  have hbasepos := hb.1.le
  have hc := coarse_shift hn1 hb.2
  have hnn : (n:ℝ)+1 ≤ 2*(n:ℝ) := by linarith only [hnp]
  calc
    _ ≤ 80*1*(B*(n:ℝ)^2)^2*(12*(2*(n:ℝ))*
      Real.exp ((2:ℕ)*((1/100:ℝ)*(n:ℝ)))*(16*Real.exp (-(n:ℝ)))) := by gcongr
    _ = (30720*B^2)*(n:ℝ)^5*Real.exp (-(49/50:ℝ)*(n:ℝ)) := by
      calc
        _ = (30720*B^2)*(n:ℝ)^5*(Real.exp ((2:ℕ)*((1/100:ℝ)*(n:ℝ)))*Real.exp (-(n:ℝ))) := by ring
        _ = _ := by rw [← Real.exp_add]; congr 2; norm_num; ring
    _ ≤ Real.exp ((23/100:ℝ)*(n:ℝ))*Real.exp (-(49/50:ℝ)*(n:ℝ)) := by gcongr
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

lemma denominator {B : ℝ} (hB : 0 < B) : ∀ᶠ n : ℕ in atTop,
    ∀ S Q F : ℝ,0 ≤ S → S ≤ Real.exp ((1/100:ℝ)*(n:ℝ)) →
      0 ≤ Q → Q ≤ B*(n:ℝ)^2 → F ≤ (n:ℝ)*Real.log n/64 →
      8*(Q*Real.exp F/(M n:ℝ)+10*(n:ℝ)⁻¹^3*Q^2*
        (12*((n:ℝ)+1)*S^2*(RadialShell.high a n*(4*Real.sqrt ε)/D)^(n-1))) ≤
      Real.exp (-(1/2:ℝ)*(n:ℝ)) := by
  filter_upwards [activity_decay hB,coarse_decay hB,
    CoveringGrowth.polynomial (C := 2) (δ := 1/4) (by norm_num) 0] with n ha hc hn S Q F hS hSb hQ hQb hF
  have h₁ := ha Q F hQ hQb hF
  have h₂ := hc S Q hS hSb hQ hQb
  have hh : 2*Real.exp (-(3/4:ℝ)*(n:ℝ)) ≤ Real.exp (-(1/2:ℝ)*(n:ℝ)) := by
    have ht := mul_le_mul_of_nonneg_right hn (Real.exp_pos (-(3/4:ℝ)*(n:ℝ))).le
    simpa only [pow_zero,mul_one,← Real.exp_add,show (1/4:ℝ)*(n:ℝ)+(-(3/4:ℝ)*(n:ℝ))=-(1/2:ℝ)*(n:ℝ) by ring] using ht
  have hs := add_le_add h₁ h₂
  have he : 8*(Q*Real.exp F/(M n:ℝ)+10*(n:ℝ)⁻¹^3*Q^2*
        (12*((n:ℝ)+1)*S^2*(RadialShell.high a n*(4*Real.sqrt ε)/D)^(n-1))) =
      8*Q*Real.exp F/(M n:ℝ)+80*(n:ℝ)⁻¹^3*Q^2*
        (12*((n:ℝ)+1)*S^2*(RadialShell.high a n*(4*Real.sqrt ε)/D)^(n-1)) := by ring
  rw [he]
  exact hs.trans (by linarith only [hh])
end NumericTail

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_SourcePatternTail
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1

namespace SourcePatternTail
open Set Metric Filter MeasureTheory SphericalLaw SourceParameters
open scoped Topology ENNReal Classical
lemma bin_count {A C : ℝ} (hA : 0 < A) (hC : 0 ≤ C) {n : ℕ}
    (hn : 1 ≤ n) (hCn : C ≤ (n:ℝ)^2) :
    (ActivityBins.count (A*C):ℝ) ≤ (A/Real.log 2+1)*(n:ℝ)^2 := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hfloor := Nat.floor_le (div_nonneg (mul_nonneg hA.le hC) hl.le)
  have hn2 : 1 ≤ (n:ℝ)^2 := one_le_pow₀ (by exact_mod_cast hn)
  dsimp [ActivityBins.count]
  push_cast
  calc
    _ ≤ A*C/Real.log 2+1 := by linarith only [hfloor]
    _ ≤ A*(n:ℝ)^2/Real.log 2+1 := by gcongr
    _ = A/Real.log 2*(n:ℝ)^2+1 := by ring
    _ ≤ A/Real.log 2*(n:ℝ)^2+(n:ℝ)^2 := by linarith only [hn2]
    _ = _ := by ring

lemma threshold_limit : ∀ᶠ n : ℕ in atTop,
    0 < RadialShell.low a n ∧
      1/Real.sqrt (1+4*ε) ≤ (1+3*RadialShell.η n)/RadialShell.high a n := by
  have hs : a < Real.sqrt (1+4*ε) := by
    apply (Real.lt_sqrt a_pos.le).mpr
    norm_num [a,ε]
  have ht : 1/Real.sqrt (1+4*ε) < 1/a := one_div_lt_one_div_of_lt a_pos hs
  have hl : Tendsto (fun n => (1+3*RadialShell.η n)/RadialShell.high a n) atTop (𝓝 (1/a)) := by
    convert ((tendsto_const_nhds (x := (1:ℝ))).add (RadialShell.eta_limit.const_mul 3)).div
      (RadialShell.high_limit a) a_pos.ne' using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | simp only [mul_zero,add_zero]
  filter_upwards [(RadialShell.low_limit a).eventually (lt_mem_nhds a_pos),hl.eventually_const_le ht] with n hn hh
  exact ⟨hn,hh⟩

theorem uniform_oai : ∃ c : ℝ,0 < c ∧ ∃ n₀ : ℕ,∀ n : ℕ,n₀ ≤ n →
    ∀ [NeZero n] [Fact (2 ≤ n)] (J : Type u_1) [Fintype J] [Nonempty J]
      (e : Sphere n) (p : J → Space n) (R : ℝ),
    0 ≤ R → R ≤ c*(n:ℝ)*Real.log n → R ≤ (n:ℝ)^2 →
    Fintype.card J ≤ N n R →
    volume (closedBall (0 : Space n) D) ≤ 4*volume
      (PatternGeometry.roundedGood p a D (RadialShell.low a n) (RadialShell.high a n) (2*Cloc*R)) →
    (BodyVolume.law e a).real (PatternTail.coverEvent p a D) ≤
      Real.exp (-Real.exp ((1/2:ℝ)*(n:ℝ))) := by
  have ha := a_pos
  let l := 1/(2*a)
  let u₀ := (1/a+1)/2
  let u := (u₀+1)/2
  have hia : 1/a < 1 := (div_lt_one a_pos).mpr a_one
  have hia0 : 0 < 1/a := one_div_pos.mpr a_pos
  have hl : 0 < l := by dsimp [l]; positivity
  have hlt : l < 1/a := by dsimp [l]; exact one_div_lt_one_div_of_lt a_pos (by linarith [a_pos])
  have hu0 : 1/a < u₀ := by dsimp [u₀]; linarith only [hia]
  have hu : u₀ < u := by dsimp [u,u₀]; linarith only [hia]
  have hu1 : u < 1 := by dsimp [u,u₀]; linarith only [hia]
  obtain ⟨K,A,H,hK,hA,hH,n₁,hbound⟩ := PatternTail.bound a_one hl hlt hu0 hu hu1
  let c : ℝ := 1/(256*A*Cloc)
  have hCloc : 0 < Cloc := by norm_num [Cloc,v]
  have hc : 0 < c := by dsimp [c]; positivity
  let B := A/Real.log 2+1
  have hB : 0 < B := by dsimp [B]; have := Real.log_pos (by norm_num : (1:ℝ)<2); positivity
  have hdim : ∀ᶠ n : ℕ in atTop,∀ R : ℝ,0 ≤ R → R ≤ c*(n:ℝ)*Real.log n → 2*Cloc*R ≤ (n:ℝ)^2 := by
    filter_upwards [RadialShell.log_div_limit.eventually_le_const (show 0<1/(2*Cloc*c) by positivity),
      eventually_ge_atTop 1] with n hn hn1 R hR hRb
    have hnp : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
    have hh := (div_le_iff₀ hnp).mp hn
    have h1 := mul_le_mul_of_nonneg_left hh (show 0 ≤ 2*Cloc*c*(n:ℝ) by positivity)
    have he : (2*Cloc*c*(n:ℝ))*(1/(2*Cloc*c)*(n:ℝ)) = (n:ℝ)^2 := by field_simp
    rw [he] at h1
    calc
      2*Cloc*R ≤ 2*Cloc*(c*(n:ℝ)*Real.log n) := by gcongr
      _ ≤ _ := by linarith only [h1]
  have hnum := NumericTail.denominator hB
  have hfine := NumericTail.fine_small hH
  have hev : ∀ᶠ n : ℕ in atTop,n₁≤n ∧ 16≤n ∧ 1≤Real.log n ∧
      (∀ R : ℝ,0≤R → R ≤ c*(n:ℝ)*Real.log n → 2*Cloc*R≤(n:ℝ)^2) ∧
      (∀ R : ℝ,0≤R → R≤(n:ℝ)^2 → (N n R:ℝ)≤Real.exp ((1/100:ℝ)*(n:ℝ))) ∧
      (0<RadialShell.low a n ∧ 1/Real.sqrt (1+4*ε)≤(1+3*RadialShell.η n)/RadialShell.high a n) ∧
      (∀ S : ℝ,0 ≤ S → S ≤ Real.exp ((1/100:ℝ)*(n:ℝ)) →
        (M n:ℝ)^2*(12*((n:ℝ)+1)*S^2*(RadialShell.high a n*(H*Real.sqrt (Real.log n/(n:ℝ)))/D)^(n-1))<1/2) ∧
      (∀ S Q F : ℝ,0≤S → S≤Real.exp ((1/100:ℝ)*(n:ℝ)) → 0≤Q → Q≤B*(n:ℝ)^2 → F≤(n:ℝ)*Real.log n/64 →
        8*(Q*Real.exp F/(M n:ℝ)+10*(n:ℝ)⁻¹^3*Q^2*(12*((n:ℝ)+1)*S^2*(RadialShell.high a n*(4*Real.sqrt ε)/D)^(n-1)))≤Real.exp (-(1/2:ℝ)*(n:ℝ))) := by
    filter_upwards [eventually_ge_atTop n₁,eventually_ge_atTop 16,
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1),
      hdim,SourceParameters.length_rate,threshold_limit,hfine,hnum] with n h1 h2 h3 h4 h5 h6 h7 h8
    exact ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨n₀,hn₀⟩ := eventually_atTop.mp hev
  refine ⟨c,hc,n₀,?_⟩
  intro n hn _ _ J _ _ e p R hR hRc hRn hcard hlarge
  obtain ⟨hn₁,hn16,hlog,hCn,hNs,hth,hfine,hden⟩ := hn₀ n hn
  let C := 2*Cloc*R
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hn1 : 1 ≤ n := by omega
  have hCdim : C ≤ (n:ℝ)^2 := hCn R hR hRc
  have hS : (Fintype.card J:ℝ) ≤ Real.exp ((1/100:ℝ)*(n:ℝ)) :=
    (by exact_mod_cast hcard : (Fintype.card J:ℝ)≤(N n R:ℝ)).trans (hNs R hR hRn)
  have hM : 2 ≤ M n := by
    have hnreal : (16:ℝ) ≤ n := by exact_mod_cast hn16
    have he : 1 ≤ (n:ℝ)*Real.log n/16 := by nlinarith only [mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (α := ℝ) n),hnreal]
    have hm := (Real.exp_one_gt_two.le.trans (Real.exp_le_exp.mpr he)).trans (NumericTail.target_count hn1).1
    exact_mod_cast hm
  have hpc : ((TargetSampling.pairs (M n)).card:ℝ) ≤ (M n:ℝ)^2 := by
    have hh := Finset.card_filter_le (Finset.univ : Finset (Fin (M n)×Fin (M n))) (fun p => p.1 ≠ p.2)
    simpa only [TargetSampling.pairs,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,pow_two] using (Nat.cast_le (α := ℝ)).mpr hh
  have hε : 0 < ε := by norm_num [ε]
  have hhigh : 0 ≤ RadialShell.high a n := by unfold RadialShell.high RadialShell.η; have := a_pos; positivity
  have hsmall := (mul_le_mul_of_nonneg_right hpc (by have := D_pos; positivity)).trans_lt (hfine (Fintype.card J) (Nat.cast_nonneg _) hS)
  have hb := hbound n hn₁ J e p D C ε (M n) D_pos hC hCdim hε (by norm_num [ε]) hM hth.1 hth.2 hlarge hsmall
  have hF : 2*A*C ≤ (n:ℝ)*Real.log n/64 := by
    have hh := mul_le_mul_of_nonneg_left hRc (show 0≤4*A*Cloc by positivity)
    have he : 4*A*Cloc*(c*(n:ℝ)*Real.log n) = (n:ℝ)*Real.log n/64 := by dsimp [c]; field_simp; ring
    rw [he] at hh
    dsimp [C]
    linarith only [hh]
  have hq0 : 0 < (ActivityBins.count (A*C):ℝ) := by dsimp [ActivityBins.count]; positivity
  have hd := hden (Fintype.card J) (ActivityBins.count (A*C)) (2*A*C) (Nat.cast_nonneg _) hS hq0.le (bin_count hA hC hn1 hCdim) hF
  apply hb.trans
  apply Real.exp_le_exp.mpr
  have hMp : 0 < (M n:ℝ) := by exact_mod_cast (by omega : 0<M n)
  have hd0 : 0 < 8*((ActivityBins.count (A*C):ℝ)*Real.exp (2*A*C)/(M n:ℝ)+10*(n:ℝ)⁻¹^3*(ActivityBins.count (A*C):ℝ)^2*(12*((n:ℝ)+1)*(Fintype.card J:ℝ)^2*(RadialShell.high a n*(4*Real.sqrt ε)/D)^(n-1))) := by have := D_pos; positivity
  have hh := neg_le_neg (one_div_le_one_div_of_le hd0 hd)
  have he : Real.exp (-(1/2:ℝ)*(n:ℝ)) = (Real.exp ((1/2:ℝ)*(n:ℝ)))⁻¹ := by rw [show -(1/2:ℝ)*(n:ℝ) = -((1/2:ℝ)*(n:ℝ)) by ring,Real.exp_neg]
  rw [he] at hh
  simpa only [neg_div,one_div,inv_inv] using hh
end SourcePatternTail

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SourcePatternTail.uniform_oai.{u_1} := @OAI.SourcePatternTail.uniform_oai.{u_1}
