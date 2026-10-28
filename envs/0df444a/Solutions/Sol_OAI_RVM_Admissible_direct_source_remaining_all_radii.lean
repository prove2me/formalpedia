-- Prove2me | solution 1 for OAI.RVM.Admissible.direct_source_remaining_all_radii
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:44:44.008033+00:00
-- url     : https://prove2.me/submissions/b40f323e-6646-4731-b628-38ff185faa0a

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000
import Theorems.Thm_OAI_RVM_Admissible_direct_source_deficit_short_sum
import Theorems.Thm_OAI_RVM_Admissible_direct_source_large_radius
import Theorems.Thm_OAI_RVM_Admissible_direct_source_relative_short_radial_sum

section
-- module Solutions.OAIQ073_VM.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_ConeMotion
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary relativistic geometry needed by the retarded-force identity. -/

noncomputable section
open MeasureTheory Set
open scoped ContDiff

namespace RVM

lemma q_pos (v : Vec) : 0 < q v := by
  exact Real.sqrt_pos.2 (by positivity)

open scoped Topology

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_RetardedPhaseDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

namespace EnergyPrefix
variable {s : Solution} {T : ℝ}

lemma particle_energy_nonneg (hs : EnergyPrefix s T) {t : ℝ} (ht : t ∈ Icc 0 T) (x : Vec) :
    0 ≤ particleEnergy s (t,x) := by
  apply integral_nonneg
  intro v
  exact mul_nonneg (q_pos v).le (hs.nonnegative t ht (x,v))

lemma total_energy_nonneg (hs : EnergyPrefix s T) {t : ℝ} (ht : t ∈ Icc 0 T) (x : Vec) :
    0 ≤ totalEnergy s (t,x) := by
  dsimp [totalEnergy]
  have hp := particle_energy_nonneg hs ht x
  positivity

end EnergyPrefix

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_DensitySecondMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma geometric_min_summable_bound {A B x y : ℝ} (hA : 0≤A) (hB : 0≤B)
    (hx : 1<x) (hy : 1<y) :
    Summable (fun k : ℤ => min (A*x^k) (B*y^(-k))) ∧
    (∑' k : ℤ, min (A*x^k) (B*y^(-k))) ≤ A/(1-x⁻¹)+B/(1-y⁻¹) := by
  let f : ℤ → ℝ := fun k => min (A*x^k) (B*y^(-k))
  have hx0 : 0<x := zero_lt_one.trans hx
  have hy0 : 0<y := zero_lt_one.trans hy
  have hxi : |x⁻¹|<1 := by rw [abs_of_pos (inv_pos.mpr hx0)]; exact inv_lt_one_of_one_lt₀ hx
  have hyi : |y⁻¹|<1 := by rw [abs_of_pos (inv_pos.mpr hy0)]; exact inv_lt_one_of_one_lt₀ hy
  have hf0 (k : ℤ) : 0≤f k := le_min (mul_nonneg hA (zpow_pos hx0 _).le) (mul_nonneg hB (zpow_pos hy0 _).le)
  have hp (n : ℕ) : f n≤B*(y⁻¹)^n := by
    calc
      _ ≤ B*y^(-(n:ℤ)) := min_le_right _ _
      _ = _ := by rw [zpow_neg,zpow_natCast,inv_pow]
  have hm (n : ℕ) : f (-(n:ℤ))≤A*(x⁻¹)^n := by
    calc
      _ ≤ A*x^(-(n:ℤ)) := min_le_left _ _
      _ = _ := by rw [zpow_neg,zpow_natCast,inv_pow]
  have hps : Summable (fun n : ℕ => f n) :=
    .of_nonneg_of_le (fun n => hf0 _) hp ((summable_geometric_of_abs_lt_one hyi).mul_left B)
  have hms : Summable (fun n : ℕ => f (-(n:ℤ))) :=
    .of_nonneg_of_le (fun n => hf0 _) hm ((summable_geometric_of_abs_lt_one hxi).mul_left A)
  have hs : Summable f := hps.of_nat_of_neg hms
  refine ⟨hs,?_⟩
  have hpb := hps.tsum_le_tsum hp ((summable_geometric_of_abs_lt_one hyi).mul_left B)
  have hmb := hms.tsum_le_tsum hm ((summable_geometric_of_abs_lt_one hxi).mul_left A)
  rw [tsum_mul_left,tsum_geometric_of_abs_lt_one hyi] at hpb
  rw [tsum_mul_left,tsum_geometric_of_abs_lt_one hxi] at hmb
  change (∑' k, f k)≤_
  rw [hps.tsum_of_nat_of_neg hms]
  change (∑' n:ℕ, f n)+(∑' n:ℕ, f (-(n:ℤ)))-f 0≤_
  simp only [div_eq_mul_inv]
  linarith [hf0 0]

lemma geometric_min_shift_bound {A B x y : ℝ} (hA : 0≤A) (hB : 0≤B)
    (hx : 1<x) (hy : 1<y) (n : ℤ) :
    (∑' k : ℤ, min (A*x^k) (B*y^(-k))) ≤
      A*x^n/(1-x⁻¹)+B*y^(-n)/(1-y⁻¹) := by
  have hn := geometric_min_summable_bound
    (mul_nonneg hA (zpow_pos (zero_lt_one.trans hx) n).le)
    (mul_nonneg hB (zpow_pos (zero_lt_one.trans hy) (-n)).le) hx hy
  have he : (fun k : ℤ => min (A*x^n*x^k) (B*y^(-n)*y^(-k))) =
      (fun k : ℤ => min (A*x^(k+n)) (B*y^(-(k+n)))) := by
    funext k
    rw [zpow_add₀ (ne_of_gt (zero_lt_one.trans hx)),neg_add,
      zpow_add₀ (ne_of_gt (zero_lt_one.trans hy))]
    congr 1 <;> ring
  rw [he] at hn
  have ht := (Equiv.addRight n).tsum_eq (fun k : ℤ => min (A*x^k) (B*y^(-k)))
  simp only [Equiv.coe_addRight] at ht
  rw [ht] at hn
  exact hn.2

lemma dyadic_balance_at {a b α β R : ℝ} (ha : 0≤a) (hb : 0≤b)
    (hα : 0<α) (hβ : 0<β) (hR : 0<R) :
    (∑' k : ℤ, min (a*((2:ℝ)^k)^α) (b*((2:ℝ)^k)^(-β))) ≤
      a*R^α/(1-(2^α)⁻¹)+2^β*(b*R^(-β))/(1-(2^β)⁻¹) := by
  obtain ⟨n,hn,hRn⟩ := exists_mem_Ico_zpow hR (by norm_num : (1:ℝ)<2)
  have hn0 : 0<(2:ℝ)^n := zpow_pos (by norm_num) _
  have hnear : a*(2^α)^n≤a*R^α := by
    rw [Real.rpow_zpow_comm (by norm_num : (0:ℝ)≤2)]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hn0.le hn hα.le) ha
  have hlow : R/2≤(2:ℝ)^n := by
    rw [zpow_add₀ (by norm_num : (2:ℝ)≠0),zpow_one] at hRn
    linarith
  have hfar : b*(2^β)^(-n)≤2^β*(b*R^(-β)) := by
    rw [Real.rpow_zpow_comm (by norm_num : (0:ℝ)≤2),zpow_neg,
      Real.inv_rpow hn0.le,← Real.rpow_neg hn0.le]
    have hh := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos (by positivity : 0<R/2) hlow (by linarith : -β≤0)) hb
    calc
      _ ≤ b*(R/2)^(-β) := hh
      _ = _ := by
        rw [Real.div_rpow hR.le (by norm_num),Real.rpow_neg (by norm_num : (0:ℝ)≤2),
          div_inv_eq_mul]
        ring
  have hsum := geometric_min_shift_bound ha hb
    (Real.one_lt_rpow (by norm_num : (1:ℝ)<2) hα) (Real.one_lt_rpow (by norm_num : (1:ℝ)<2) hβ) n
  have hfun : (fun k : ℤ => min (a*(2^α)^k) (b*(2^β)^(-k))) =
      (fun k : ℤ => min (a*((2:ℝ)^k)^α) (b*((2:ℝ)^k)^(-β))) := by
    funext k
    rw [Real.rpow_zpow_comm (by norm_num : (0:ℝ)≤2),
      Real.rpow_zpow_comm (by norm_num : (0:ℝ)≤2),zpow_neg,
      Real.inv_rpow (zpow_pos (by norm_num : (0:ℝ)<2) k).le,
      Real.rpow_neg (zpow_pos (by norm_num : (0:ℝ)<2) k).le]
  rw [hfun] at hsum
  have hx : 0≤1-((2:ℝ)^α)⁻¹ := by
    have hh := inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (by norm_num : (1:ℝ)<2) hα)
    linarith
  have hy : 0≤1-((2:ℝ)^β)⁻¹ := by
    have hh := inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (by norm_num : (1:ℝ)<2) hβ)
    linarith
  exact hsum.trans (add_le_add (div_le_div_of_nonneg_right hnear hx)
    (div_le_div_of_nonneg_right hfar hy))

lemma dyadic_balance {a b α β : ℝ} (ha : 0<a) (hb : 0<b)
    (hα : 0<α) (hβ : 0<β) :
    (∑' k : ℤ, min (a*((2:ℝ)^k)^α) (b*((2:ℝ)^k)^(-β))) ≤
      ((1-(2^α)⁻¹)⁻¹+2^β/(1-(2^β)⁻¹)) *
        (a^(β/(α+β))*b^(α/(α+β))) := by
  let R : ℝ := (b/a)^(1/(α+β))
  have hR : 0<R := Real.rpow_pos_of_pos (div_pos hb ha) _
  have hab : α+β≠0 := ne_of_gt (add_pos hα hβ)
  have hpow₁ : a*R^α = a^(β/(α+β))*b^(α/(α+β)) := by
    dsimp [R]
    rw [← Real.rpow_mul (div_pos hb ha).le]
    have he : 1/(α+β)*α = α/(α+β) := by ring
    have he' : β/(α+β) = 1-α/(α+β) := by field_simp; ring
    rw [he, Real.div_rpow hb.le ha.le, he', Real.rpow_sub ha, Real.rpow_one]
    ring
  have hpow₂ : b*R^(-β) = a^(β/(α+β))*b^(α/(α+β)) := by
    dsimp [R]
    rw [← Real.rpow_mul (div_pos hb ha).le]
    have he : 1/(α+β)*(-β) = -(β/(α+β)) := by ring
    have he' : α/(α+β) = 1-β/(α+β) := by field_simp; ring
    rw [he, Real.rpow_neg (div_pos hb ha).le,Real.div_rpow hb.le ha.le,
      inv_div,he',Real.rpow_sub hb,Real.rpow_one]
    ring
  have hh := dyadic_balance_at ha.le hb.le hα hβ hR
  rw [hpow₁,hpow₂] at hh
  convert hh using 1 <;> first | rfl | ring

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_DyadicBalanceConstant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open scoped Topology ContDiff ENNReal
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma dyadicBalanceConstant_pos {α β : ℝ} (hα : 0<α) (hβ : 0<β) :
    0<dyadicBalanceConstant α β := by
  have ha : 0<1-((2:ℝ)^α)⁻¹ := sub_pos.mpr
    (inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (by norm_num : (1:ℝ)<2) hα))
  have hb : 0<1-((2:ℝ)^β)⁻¹ := sub_pos.mpr
    (inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (by norm_num : (1:ℝ)<2) hβ))
  unfold dyadicBalanceConstant
  positivity

lemma dyadic_power_min_summable {a b α β : ℝ} (ha : 0≤a) (hb : 0≤b)
    (hα : 0<α) (hβ : 0<β) :
    Summable (fun k : ℤ => min (a*((2:ℝ)^k)^α) (b*((2:ℝ)^k)^(-β))) := by
  have hh := (geometric_min_summable_bound ha hb
    (Real.one_lt_rpow (by norm_num : (1:ℝ)<2) hα)
    (Real.one_lt_rpow (by norm_num : (1:ℝ)<2) hβ)).1
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext k
  rw [Real.rpow_zpow_comm (by norm_num : (0:ℝ)≤2),
    Real.rpow_zpow_comm (by norm_num : (0:ℝ)≤2),zpow_neg,
    Real.inv_rpow (zpow_pos (by norm_num : (0:ℝ)<2) k).le,
    Real.rpow_neg (zpow_pos (by norm_num : (0:ℝ)<2) k).le]

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_SelectionWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ContDiff
open Filter Set
open scoped Topology

namespace RVM

lemma div_stabilityLength (P C₁ M A p w φ t : ℝ) :
    t/stabilityLength P C₁ M A p w φ =
      t*(stabilityRate P C₁ M A p w φ)^2 := by
  simp [stabilityLength, div_eq_mul_inv, inv_pow]

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_NormalisedPartialCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma product_le_min_scale {P p w : ℝ} (hp : 0≤p) (hw : 0≤w)
    (hpP : p≤P) (hwP : w≤P) : w*p≤P*min p w := by
  rcases le_total p w with h|h
  · rw [min_eq_left h]
    exact mul_le_mul_of_nonneg_right hwP hp
  · rw [min_eq_right h]
    calc w*p≤w*P := mul_le_mul_of_nonneg_left hpP hw
         _ = P*w := by ring

lemma sqrt_div_stabilityLength {P C M A p w φ I : ℝ}
    (hP : 0≤P) (hC : 0≤C) (hM : 0≤M) (hp : 0≤p) (hw : 0≤w)
    (hφ : 0≤φ) (hI : 0≤I) :
    Real.sqrt (I/stabilityLength P C M A p w φ)=
      Real.sqrt I*stabilityRate P C M A p w φ := by
  rw [div_stabilityLength,Real.sqrt_mul hI,Real.sqrt_sq]
  unfold stabilityRate
  positivity

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_SqrtBaselineClippedLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma sqrt_baseline_clipped_length {I lam : ℝ} (hI : 0 < I) (hlam : 0 < lam) :
    Real.sqrt (1+I/min I (lam/2))  ≤  2*(1+Real.sqrt (I/lam)) := by
  have hlen : 0 < min I (lam/2) := lt_min hI (by positivity)
  have hq : 0 ≤ I/lam := by positivity
  have hR : 0 ≤ Real.sqrt (I/lam) := Real.sqrt_nonneg _
  have hRsq := Real.sq_sqrt hq
  have hdiv : I/min I (lam/2)  ≤  1+2*(I/lam) := by
    rcases le_total I (lam/2) with h|h
    · rw [min_eq_left h,div_self hI.ne']
      linarith
    · rw [min_eq_right h]
      have he : I/(lam/2)=2*(I/lam) := by ring
      rw [he]
      linarith
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity,?_⟩
  nlinarith

lemma stabilityLength_pos {P C M A p w φ : ℝ} (hP : 0 < P) (hC : 0 < C)
    (hM : 0 < M) (hp : 0 < p) (hw : 0 < w) (hφ : 0 < φ) :
    0 < stabilityLength P C M A p w φ := by
  unfold stabilityLength stabilityRate
  have hm : 0 < min p w := lt_min hp hw
  have hr : 0  <  M/φ+Real.sqrt (A*Real.log (2+P)/φ) :=
    add_pos_of_pos_of_nonneg (div_pos hM hφ) (Real.sqrt_nonneg _)
  positivity

lemma stability_massScale_identity (P C M A p w φ : ℝ) :
    (C*(P/(min p w/128))*(M/φ+Real.sqrt (A*Real.log (2+P)/φ)))⁻¹^2 =
      stabilityLength P (128*C) M A p w φ := by
  unfold stabilityLength stabilityRate
  congr 2
  ring

lemma direction_baseline_R_bound128 {P C M A p w φ : ℝ}
    (hP : 0<P) (hC : 0≤C) (hM : 0≤M) (hA : 0≤A)
    (hp : 0<p) (hw : 0<w) (hφ : 0<φ) (hφ1 : φ≤1)
    (hpP : p≤128*P) (hwP : w≤P) :
    Real.sqrt ((w/P)^2)*(1+Real.sqrt (((w/P)^2)/stabilityLength P C M A p w φ))*p*φ≤
      128*w*(1+C*(M+Real.sqrt (A*Real.log (2+P)))) := by
  have hL : 0≤Real.log (2+P) := Real.log_nonneg (by linarith)
  have hm : 0 < min p w := lt_min hp hw
  have hwP' : w≤128*P := hwP.trans (by linarith only [hP])
  have hwp := product_le_min_scale hp.le hw.le hpP hwP'
  have hmain : w^2*p/(P*min p w)≤128*w := by
    apply (div_le_iff₀ (mul_pos hP hm)).mpr
    nlinarith
  have hfirst : w*p*φ/P≤128*w := by
    apply (div_le_iff₀ hP).mpr
    have hh : p*φ≤128*P := (mul_le_of_le_one_right hp.le hφ1).trans hpP
    nlinarith
  have hroot : φ*Real.sqrt (A*Real.log (2+P)/φ)=
      Real.sqrt (A*Real.log (2+P)*φ) := by
    calc
      _ = Real.sqrt (φ^2)*Real.sqrt (A*Real.log (2+P)/φ) := by rw [Real.sqrt_sq hφ.le]
      _ = Real.sqrt (A*Real.log (2+P)*φ) := by
        rw [←Real.sqrt_mul (sq_nonneg φ)]
        congr 1
        field_simp
  have hsqrt : Real.sqrt (A*Real.log (2+P)*φ)≤Real.sqrt (A*Real.log (2+P)) :=
    Real.sqrt_le_sqrt (mul_le_of_le_one_right (mul_nonneg hA hL) hφ1)
  rw [Real.sqrt_sq (div_nonneg hw.le hP.le),
    sqrt_div_stabilityLength hP.le hC hM hp.le hw.le hφ.le (sq_nonneg _),
    Real.sqrt_sq (div_nonneg hw.le hP.le)]
  have he : (w/P)*(1+(w/P)*stabilityRate P C M A p w φ)*p*φ=
      w*p*φ/P+C*(w^2*p/(P*min p w))*(M+φ*Real.sqrt (A*Real.log (2+P)/φ)) := by
    unfold stabilityRate
    field_simp
  rw [he,hroot]
  calc
    _ ≤ 128*w+C*(128*w)*(M+Real.sqrt (A*Real.log (2+P))) := by gcongr
    _ = _ := by ring

lemma direction_baseline_R_log_bound128 {P C M A p w φ : ℝ}
    (hP : 0<P) (hL : 1≤Real.log (2+P)) (hC : 0≤C) (hM : 0≤M) (hA : 0≤A)
    (hp : 0<p) (hw : 0<w) (hφ : 0<φ) (hφ1 : φ≤1)
    (hpP : p≤128*P) (hwP : w≤P) :
    Real.sqrt ((w/P)^2)*(1+Real.sqrt (((w/P)^2)/stabilityLength P C M A p w φ))*p*φ≤
      128*(1+C*(M+Real.sqrt A))*w*Real.sqrt (Real.log (2+P)) := by
  apply (direction_baseline_R_bound128 hP hC hM hA hp hw hφ hφ1 hpP hwP).trans
  rw [Real.sqrt_mul hA]
  have hroot : 1≤Real.sqrt (Real.log (2+P)) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hL
  have h0 : 0≤1+C*M := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hroot (mul_nonneg (show 0≤128*w by positivity) h0)]

lemma direction_clipped_baseline_R_log_bound128 {P C M A p w φ : ℝ}
    (hP : 0 < P) (hL : 1 ≤ Real.log (2+P)) (hC : 0 < C) (hM : 0 < M) (hA : 0 ≤ A)
    (hp : 0 < p) (hw : 0 < w) (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hpP : p ≤ 128*P) (hwP : w ≤ P) :
    let I := (w/P)^2
    let lam := stabilityLength P C M A p w φ
    Real.sqrt I*Real.sqrt (1+I/min I (lam/2))*p*φ  ≤
      256*(1+C*(M+Real.sqrt A))*w*Real.sqrt (Real.log (2+P)) := by
  dsimp only
  have hI : 0 < (w/P)^2 := sq_pos_of_pos (div_pos hw hP)
  have hlam := stabilityLength_pos hP hC hM hp hw hφ (A:=A)
  have hroot := sqrt_baseline_clipped_length hI hlam
  have hbound := direction_baseline_R_log_bound128 hP hL hC.le hM.le hA hp hw hφ hφ1 hpP hwP
  calc
    _  ≤  Real.sqrt ((w/P)^2)*(2*(1+Real.sqrt (((w/P)^2)/stabilityLength P C M A p w φ)))*p*φ := by gcongr
    _ = 2*(Real.sqrt ((w/P)^2)*(1+Real.sqrt (((w/P)^2)/stabilityLength P C M A p w φ))*p*φ) := by ring
    _  ≤  2*(128*(1+C*(M+Real.sqrt A))*w*Real.sqrt (Real.log (2+P))) := by gcongr
    _ = _ := by ring

end RVM

end

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma remaining_good_angular {θ φ σ κ : ℝ} (hθ : 0≤θ) (hφ : 0≤φ)
    (hσ : 0<σ) (_hκ : 0≤κ) (hφθ : φ≤κ*θ) :
    (min θ σ)^3*φ^2*Real.sqrt (1+φ/σ)≤κ^2*(1+κ)*σ*θ^4 := by
  let ν := min θ σ
  have hν : 0≤ν := le_min hθ hσ.le
  have hnθ : ν≤θ := min_le_left _ _
  have hnσ : ν≤σ := min_le_right _ _
  have hroot : Real.sqrt (1+φ/σ)≤1+φ/σ :=
    Real.sqrt_le_self_iff.mpr (Or.inr (le_add_of_nonneg_right (div_nonneg hφ hσ.le)))
  have hc1 : ν^3≤σ*θ^2 := by
    calc
      _ = ν*ν^2 := by ring
      _ ≤ σ*θ^2 := by gcongr
  have hc2 : ν^3≤σ^2*θ := by
    calc
      _ = ν^2*ν := by ring
      _ ≤ σ^2*θ := by gcongr
  have h1 : ν^3*φ^2≤κ^2*σ*θ^4 := by
    calc
      _ ≤ (σ*θ^2)*(κ*θ)^2 := mul_le_mul hc1 (by gcongr) (sq_nonneg _) (by positivity)
      _ = _ := by ring
  have h2 : ν^3*φ^3/σ≤κ^3*σ*θ^4 := by
    calc
      _ ≤ (σ^2*θ)*(κ*θ)^3/σ := by gcongr
      _ = _ := by field_simp
  change ν^3*φ^2*Real.sqrt (1+φ/σ)≤_
  calc
    _ ≤ ν^3*φ^2*(1+φ/σ) := mul_le_mul_of_nonneg_left hroot (by positivity)
    _ = ν^3*φ^2+ν^3*φ^3/σ := by ring
    _ ≤ κ^2*σ*θ^4+κ^3*σ*θ^4 := add_le_add h1 h2
    _ = _ := by ring

lemma remaining_magnetic_angular {θ φ σ κ : ℝ} (hθ : 0≤θ) (hθ1 : θ≤1)
    (hφ : 0≤φ) (hσ : 0<σ) (hκ : 0≤κ) (hφθ : φ≤κ*θ) :
    (min θ σ)^3*Real.sqrt (1+φ/σ)≤(1+κ)*σ := by
  let ν := min θ σ
  have hν : 0≤ν := le_min hθ hσ.le
  have hnθ : ν≤θ := min_le_left _ _
  have hnσ : ν≤σ := min_le_right _ _
  have hroot : Real.sqrt (1+φ/σ)≤1+φ/σ :=
    Real.sqrt_le_self_iff.mpr (Or.inr (le_add_of_nonneg_right (div_nonneg hφ hσ.le)))
  have hc1 : ν^3≤σ*θ^2 := by
    calc
      _ = ν*ν^2 := by ring
      _ ≤ σ*θ^2 := by gcongr
  have hc2 : ν^3≤σ^2*θ := by
    calc
      _ = ν^2*ν := by ring
      _ ≤ σ^2*θ := by gcongr
  have hθ2 : θ^2≤1 := by nlinarith
  have h1 : ν^3≤σ := hc1.trans (by nlinarith)
  have h2 : ν^3*φ/σ≤κ*σ := by
    calc
      _ ≤ (σ^2*θ)*(κ*θ)/σ := by gcongr
      _ = κ*σ*θ^2 := by field_simp
      _ ≤ κ*σ := by nlinarith [mul_nonneg hκ hσ.le]
  change ν^3*Real.sqrt (1+φ/σ)≤_
  calc
    _ ≤ ν^3*(1+φ/σ) := mul_le_mul_of_nonneg_left hroot (by positivity)
    _ = ν^3+ν^3*φ/σ := by ring
    _ ≤ σ+κ*σ := add_le_add h1 h2
    _ = _ := by ring

lemma direction_interval_momentum_factor {P p w : ℝ}
    (hP : 0<P) (hp : 0≤p) (hw : 0≤w) (hpP : p≤128*P) (hwP : w≤P) :
    (w/P)^2*p≤128*w := by
  have hwq : w/P≤1 := (div_le_one hP).mpr hwP
  have hpq : p/P≤128 := (div_le_iff₀ hP).mpr hpP
  calc
    _ = (w/P)*w*(p/P) := by ring
    _ ≤ 1*w*128 := by gcongr
    _ = _ := by ring

lemma remaining_good_balance_coefficient {P C M A p w θ φ σ κ : ℝ}
    (hP : 0<P) (hL : 1≤Real.log (2+P)) (hC : 0<C) (hM : 0<M) (hA : 0≤A)
    (hp : 0<p) (hw : 0<w) (hθ : 0<θ) (hφ : 0≤φ) (hσ : 0<σ) (hσ1 : σ≤1)
    (hκ : 0≤κ) (hφθ : φ≤κ*θ) (hpP : p≤128*P) (hwP : w≤P) :
    let I := (w/P)^2
    let R := Real.sqrt (1+I/min I (stabilityLength P C M A p w σ/2))
    I*Real.sqrt I*R*p^2*((min θ σ)^3*φ^2*Real.sqrt (1+φ/σ)/θ^4)≤
      32768*κ^2*(1+κ)*(1+C*(M+Real.sqrt A))*w^2*Real.sqrt (Real.log (2+P)) := by
  let I := (w/P)^2
  let R := Real.sqrt (1+I/min I (stabilityLength P C M A p w σ/2))
  change I*Real.sqrt I*R*p^2*((min θ σ)^3*φ^2*Real.sqrt (1+φ/σ)/θ^4)≤_
  have hI : 0≤I := sq_nonneg _
  have hR : 0≤R := Real.sqrt_nonneg _
  have hang : (min θ σ)^3*φ^2*Real.sqrt (1+φ/σ)/θ^4≤κ^2*(1+κ)*σ := by
    apply (div_le_iff₀ (pow_pos hθ 4)).mpr
    exact remaining_good_angular hθ.le hφ hσ hκ hφθ
  have hrate := direction_clipped_baseline_R_log_bound128 hP hL hC hM hA hp hw hσ hσ1 hpP hwP
  change Real.sqrt I*R*p*σ≤_ at hrate
  have hIp := direction_interval_momentum_factor hP hp.le hw.le hpP hwP
  change I*p≤_ at hIp
  calc
    _ ≤ I*Real.sqrt I*R*p^2*(κ^2*(1+κ)*σ) := by gcongr
    _ = (κ^2*(1+κ))*(I*p)*(Real.sqrt I*R*p*σ) := by ring
    _ ≤ (κ^2*(1+κ))*(128*w)*
        (256*(1+C*(M+Real.sqrt A))*w*Real.sqrt (Real.log (2+P))) := by gcongr
    _ = _ := by ring

lemma remaining_magnetic_balance_coefficient {P C M A p w θ φ σ κ : ℝ}
    (hP : 0<P) (hL : 1≤Real.log (2+P)) (hC : 0<C) (hM : 0<M) (hA : 0≤A)
    (hp : 0<p) (hw : 0<w) (hθ : 0≤θ) (hθ1 : θ≤1) (hφ : 0≤φ) (hσ : 0<σ) (hσ1 : σ≤1)
    (hκ : 0≤κ) (hφθ : φ≤κ*θ) (hpP : p≤128*P) (hwP : w≤P) :
    let I := (w/P)^2
    let R := Real.sqrt (1+I/min I (stabilityLength P C M A p w σ/2))
    I*Real.sqrt I*R*p^2*((min θ σ)^3*Real.sqrt (1+φ/σ))≤
      32768*(1+κ)*(1+C*(M+Real.sqrt A))*w^2*Real.sqrt (Real.log (2+P)) := by
  let I := (w/P)^2
  let R := Real.sqrt (1+I/min I (stabilityLength P C M A p w σ/2))
  change I*Real.sqrt I*R*p^2*((min θ σ)^3*Real.sqrt (1+φ/σ))≤_
  have hI : 0≤I := sq_nonneg _
  have hR : 0≤R := Real.sqrt_nonneg _
  have hang := remaining_magnetic_angular hθ hθ1 hφ hσ hκ hφθ
  have hrate := direction_clipped_baseline_R_log_bound128 hP hL hC hM hA hp hw hσ hσ1 hpP hwP
  change Real.sqrt I*R*p*σ≤_ at hrate
  have hIp := direction_interval_momentum_factor hP hp.le hw.le hpP hwP
  change I*p≤_ at hIp
  calc
    _ ≤ I*Real.sqrt I*R*p^2*((1+κ)*σ) := by gcongr
    _ = (1+κ)*(I*p)*(Real.sqrt I*R*p*σ) := by ring
    _ ≤ (1+κ)*(128*w)*
        (256*(1+C*(M+Real.sqrt A))*w*Real.sqrt (Real.log (2+P))) := by gcongr
    _ = _ := by ring

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_PhysicalDirectTransportDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma dyadic_sqrt_radius_balance {a b H : ℝ} (ha : 0≤a) (hb : 0≤b) (hH : 0<H) :
    Summable (fun k : ℤ=>min (a*Real.sqrt (H*(2:ℝ)^k))
      (b/Real.sqrt (H*(2:ℝ)^k))) ∧
    (∑'k : ℤ,min (a*Real.sqrt (H*(2:ℝ)^k))
      (b/Real.sqrt (H*(2:ℝ)^k)))≤dyadicBalanceConstant (1/2) (1/2)*Real.sqrt (a*b) := by
  let a' := a*Real.sqrt H
  let b' := b/Real.sqrt H
  have hHroot : 0<Real.sqrt H := Real.sqrt_pos.mpr hH
  have he (k : ℤ) : min (a'*((2:ℝ)^k)^(1/2:ℝ)) (b'*((2:ℝ)^k)^(-(1/2:ℝ)))=
      min (a*Real.sqrt (H*(2:ℝ)^k)) (b/Real.sqrt (H*(2:ℝ)^k)) := by
    rw [Real.rpow_neg (zpow_pos (by norm_num : (0:ℝ)<2) k).le]
    rw [←Real.sqrt_eq_rpow,Real.sqrt_mul hH.le]
    dsimp [a',b']
    congr 1 <;> ring
  have hs := dyadic_power_min_summable (mul_nonneg ha hHroot.le)
    (div_nonneg hb hHroot.le) (by norm_num : (0:ℝ)<1/2) (by norm_num : (0:ℝ)<1/2)
  change Summable (fun k : ℤ=>min (a'*((2:ℝ)^k)^(1/2:ℝ)) (b'*((2:ℝ)^k)^(-(1/2:ℝ)))) at hs
  simp_rw [he] at hs
  refine ⟨hs,?_⟩
  rcases eq_or_lt_of_le ha with rfl|ha'
  · have he0 (k : ℤ) : min (0*Real.sqrt (H*(2:ℝ)^k)) (b/Real.sqrt (H*(2:ℝ)^k))=0 := by
      rw [zero_mul,min_eq_left (by positivity)]
    rw [tsum_congr he0]
    simp
  rcases eq_or_lt_of_le hb with rfl|hb'
  · have he0 (k : ℤ) : min (a*Real.sqrt (H*(2:ℝ)^k)) (0/Real.sqrt (H*(2:ℝ)^k))=0 := by
      rw [zero_div,min_eq_right (by positivity)]
    rw [tsum_congr he0]
    simp
  have ht := dyadic_balance (mul_pos ha' hHroot) (div_pos hb' hHroot)
    (by norm_num : (0:ℝ)<1/2) (by norm_num : (0:ℝ)<1/2)
  change (∑'k : ℤ,min (a'*((2:ℝ)^k)^(1/2:ℝ)) (b'*((2:ℝ)^k)^(-(1/2:ℝ))))≤_ at ht
  simp_rw [he] at ht
  norm_num only [show (1/2:ℝ)+(1/2)=1 by norm_num,div_one] at ht
  change (∑'k : ℤ,min (a*Real.sqrt (H*(2:ℝ)^k)) (b/Real.sqrt (H*(2:ℝ)^k)))≤
    dyadicBalanceConstant (1/2) (1/2)*(a'^(1/2:ℝ)*b'^(1/2:ℝ)) at ht
  rw [←Real.sqrt_eq_rpow a',←Real.sqrt_eq_rpow b',←Real.sqrt_mul (by positivity : 0≤a')] at ht
  have hab : a'*b'=a*b := by dsimp [a',b']; field_simp
  rw [hab] at ht
  exact ht

end RVM

end

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_CappedRepresentativePos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma cappedRepresentative_pos (n : ℕ) : 0 < cappedRepresentative n := by
  dsimp [cappedRepresentative]
  positivity

lemma cappedRepresentative_le_one (n : ℕ) : cappedRepresentative n ≤ 1 := by
  exact pow_le_one₀ (by norm_num) (by norm_num)

end RVM

end

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Flow_ClosedEulerianTimeBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma large_radius_magnetic_coefficient {H p ν θ φ : ℝ}
    (hH : 0<H) (hp : 0<p) (hν : 0<ν) (hθ : 0<θ) (hφ : 0<φ) :
    (H*p^2*ν^2*φ)^(1/3:ℝ)*(Real.sqrt p*ν/(θ*Real.sqrt H))^(2/3:ℝ)=
      p*ν^(4/3:ℝ)*θ^(-(2/3:ℝ))*φ^(1/3:ℝ) := by
  rw [Real.div_rpow (by positivity) (by positivity),
    Real.mul_rpow (by positivity : 0≤H*p^2*ν^2) hφ.le,
    Real.mul_rpow (by positivity : 0≤H*p^2) (sq_nonneg ν),
    Real.mul_rpow hH.le (sq_nonneg p),
    Real.mul_rpow (Real.sqrt_nonneg p) hν.le,
    Real.mul_rpow hθ.le (Real.sqrt_nonneg H),
    Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,
    ←Real.rpow_natCast_mul hp.le,←Real.rpow_natCast_mul hν.le,
    ←Real.rpow_mul hp.le,←Real.rpow_mul hH.le,Real.rpow_neg hθ.le]
  norm_num only [Nat.cast_ofNat,show (2:ℝ)*(1/3)=2/3 by norm_num,
    show (1/2:ℝ)*(2/3)=1/3 by norm_num]
  have hpp : p^(2/3:ℝ)*p^(1/3:ℝ)=p := by
    rw [←Real.rpow_add hp]; norm_num
  have hνν : ν^(2/3:ℝ)*ν^(2/3:ℝ)=ν^(4/3:ℝ) := by
    rw [←Real.rpow_add hν]; congr 1; norm_num
  have hHp : H^(1/3:ℝ)≠0 := (Real.rpow_pos_of_pos hH _).ne'
  have hθp : θ^(2/3:ℝ)≠0 := (Real.rpow_pos_of_pos hθ _).ne'
  calc
    _ = (p^(2/3:ℝ)*p^(1/3:ℝ))*(ν^(2/3:ℝ)*ν^(2/3:ℝ))*
        (θ^(2/3:ℝ))⁻¹*φ^(1/3:ℝ) := by field_simp [hHp,hθp]
    _ = _ := by rw [hpp,hνν]

lemma large_radius_magnetic_balance {H p θ φ σ : ℝ}
    (hH : 0<H) (hp : 0<p) (hθ : 0<θ) (hφ : 0<φ) (hσ : 0<σ) :
    let ν := min θ σ
    Summable (fun k : ℤ=>min (H*(2:ℝ)^k*p^2*ν^2*φ)
      (Real.sqrt p*ν/(θ*Real.sqrt (H*(2:ℝ)^k)))) ∧
    (∑'k : ℤ,min (H*(2:ℝ)^k*p^2*ν^2*φ)
      (Real.sqrt p*ν/(θ*Real.sqrt (H*(2:ℝ)^k))))≤
      dyadicBalanceConstant 1 (1/2)*(p*ν^(4/3:ℝ)*θ^(-(2/3:ℝ))*φ^(1/3:ℝ)) := by
  dsimp only
  let ν := min θ σ
  have hν : 0<ν := lt_min hθ hσ
  let a := H*p^2*ν^2*φ
  let b := Real.sqrt p*ν/(θ*Real.sqrt H)
  have ha : 0<a := by dsimp only [a]; positivity
  have hb : 0<b := by dsimp only [b]; positivity
  have he (k : ℤ) : min (a*((2:ℝ)^k)^(1:ℝ)) (b*((2:ℝ)^k)^(-(1/2:ℝ)))=
      min (H*(2:ℝ)^k*p^2*ν^2*φ) (Real.sqrt p*ν/(θ*Real.sqrt (H*(2:ℝ)^k))) := by
    rw [Real.rpow_one,Real.rpow_neg (zpow_pos (by norm_num : (0:ℝ)<2) k).le,
      ←Real.sqrt_eq_rpow,Real.sqrt_mul hH.le]
    dsimp only [a,b]
    congr 1 <;> ring
  have hs := dyadic_power_min_summable ha.le hb.le (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<1/2)
  have ht := dyadic_balance ha hb (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<1/2)
  simp_rw [he] at hs ht
  refine ⟨hs,?_⟩
  rw [show (1/2:ℝ)/(1+1/2)=1/3 by norm_num,
    show (1:ℝ)/(1+1/2)=2/3 by norm_num] at ht
  change _≤dyadicBalanceConstant 1 (1/2)*(a^(1/3:ℝ)*b^(2/3:ℝ)) at ht
  dsimp only [a,b] at ht
  rwa [large_radius_magnetic_coefficient hH hp hν hθ hφ] at ht

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_LocalPDE_RelativeCauchyConstant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma relativeCauchyConstant_nonneg {C E Z : ℝ} (hC : 0≤C) :
    0 ≤ relativeCauchyConstant C E Z := by unfold relativeCauchyConstant; positivity

lemma capped_sqrt_radius_ennreal_sum {a b H K : ℝ}
    (ha : 0≤a) (hb : 0≤b) (hH : 0<H) (hK : 0≤K) :
    (∑'n : ℕ, ENNReal.ofReal (K*min (a*Real.sqrt (H*cappedRepresentative n))
      (b/Real.sqrt (H*cappedRepresentative n)))) ≤
      ENNReal.ofReal (K*dyadicBalanceConstant (1/2) (1/2)*Real.sqrt (a*b)) := by
  let g : ℤ→ℝ := fun k=>min (a*Real.sqrt (H*(2:ℝ)^k)) (b/Real.sqrt (H*(2:ℝ)^k))
  have hg0 (k : ℤ) : 0≤g k := by dsimp [g]; positivity
  have hg := dyadic_sqrt_radius_balance ha hb hH
  have he (n : ℕ) : cappedRepresentative n=(2:ℝ)^(-(n:ℤ)) := by
    simp only [cappedRepresentative,zpow_neg,zpow_natCast,inv_pow]
  have hinj : Function.Injective (fun n : ℕ=>-(n:ℤ)) := by
    intro a b hab
    exact_mod_cast neg_injective hab
  calc
    _ = ∑'n : ℕ,ENNReal.ofReal (K*g (-(n:ℤ))) := by
      apply tsum_congr
      intro n
      rw [he]
    _ ≤ ∑'k : ℤ,ENNReal.ofReal (K*g k) :=
      ENNReal.tsum_comp_le_tsum_of_injective hinj (fun k=>ENNReal.ofReal (K*g k))
    _ = ENNReal.ofReal (K*∑'k : ℤ,g k) := by
      rw [←ENNReal.ofReal_tsum_of_nonneg (fun k=>mul_nonneg hK (hg0 k)) (hg.1.mul_left K),tsum_mul_left]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      simpa only [g,mul_assoc] using mul_le_mul_of_nonneg_left hg.2 hK

lemma Admissible.direct_source_remaining_short_sum {d : Datum} (hd₀ : Admissible d) :
    ∃ Cg Cb : ℝ, 0 ≤ Cg ∧ 0 ≤ Cb ∧
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀ z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (S : Set Phase) (np nθ nφ j : ℕ) (a b w M A P : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → a ≤ b → b-a ≤ (w/P)^2 →
      0 < M → 0 ≤ A → 0 < P → 1 ≤ Real.log (2+P) → 0 < w → w≤P →
      sourceRepresentative np≤128*P →
      cappedRepresentative nφ≤16*cappedRepresentative nθ →
      512 ≤ cappedRepresentative j*sourceRepresentative np →
      32 ≤ cappedRepresentative j*w →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := fun nr=>relativeRepresentativeClosedBin T w ![np,nθ,nφ,nr] j
      let E := ∫x : Vec,totalEnergy s (0,x)
      let Kg := relativeCauchyConstant Cg E (20*E)
      let Kb := relativeCauchyConstant Cb E (120*E)
      (∑'nr : ℕ,if max 1 T*cappedRepresentative nr≤(w/P)^2 then
        ∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V (B nr) z
          ∂physicalBinMeasure V (B nr) (Icc a b) else 0) ≤
      ENNReal.ofReal ((16*Kg+Kb)*dyadicBalanceConstant (1/2) (1/2)*
        Real.sqrt (32768*17*(1+16384*(M+Real.sqrt A))*w^2*Real.sqrt (Real.log (2+P)))) := by
  obtain ⟨Cg,Cb,hCg,hCb,hsource⟩ := hd₀.direct_source_relative_short_radial_sum
  refine ⟨Cg,Cb,hCg,hCb,?_⟩
  intro s T F hs hT h0 zX S np nθ nφ j a b w M A P hS hS0 ha hb hab hJI
    hM hA hP hL hw hwP hpP hφθ hpσ hwσ HX HZ
  dsimp only
  let p := sourceRepresentative np
  let θ := cappedRepresentative nθ
  let φ := cappedRepresentative nφ
  let σ := cappedRepresentative j
  let L := Real.log (2+P)
  let I := (w/P)^2
  let lam := stabilityLength P 16384 M A p w σ
  let len := min I (lam/2)
  let m := min p w/128
  let E := ∫x : Vec,totalEnergy s (0,x)
  let R := Real.sqrt (1+I/len)
  let ν := min θ σ
  let Kg := relativeCauchyConstant Cg E (20*E)
  let Kb := relativeCauchyConstant Cb E (120*E)
  let D := dyadicBalanceConstant (1/2) (1/2)
  let U := 32768*17*(1+16384*(M+Real.sqrt A))*w^2*Real.sqrt L
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  have hθ : 0<θ := cappedRepresentative_pos _
  have hφ : 0<φ := cappedRepresentative_pos _
  have hσ : 0<σ := cappedRepresentative_pos _
  have hI : 0<I := sq_pos_of_pos (div_pos hw hP)
  have hlam : 0<lam := stabilityLength_pos hP (by norm_num) hM hp hw hσ
  have hlen : 0<len := lt_min hI (by positivity)
  have hlenI : len≤I := min_le_left _ _
  have hlenlam : 2*len≤lam := by
    have hh : len≤lam/2 := min_le_right _ _
    linarith only [hh]
  have hm : 0 < m := div_pos (lt_min hp hw) (by norm_num)
  have hmq : m≤p/128 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hmw : m≤w/8 := by
    have hh : min p w≤w := min_le_right _ _
    dsimp [m]
    linarith only [hh,hw]
  have hstable : 2*len≤(128*(P/m)*(M/σ+Real.sqrt (A*L/σ)))⁻¹^2 := by
    dsimp only [m,L]
    rw [stability_massScale_identity]
    convert hlenlam using 1; norm_num [lam]
  have hn := hsource s T F hs hT h0 zX S np nθ nφ j a b I len w M A P L m 128
    hS hS0 ha hb hab hlen hlenI hJI hM hA hP (by dsimp [L]; linarith only [hL]) hm hw
    (by norm_num) hmq hmw hpσ hwσ hstable HX HZ
  have hg := remaining_good_balance_coefficient hP hL (show (0:ℝ)<16384 by norm_num)
    hM hA hp hw hθ hφ.le hσ (cappedRepresentative_le_one _) (by norm_num : (0:ℝ)≤16) hφθ hpP hwP
  have hb' := remaining_magnetic_balance_coefficient hP hL (show (0:ℝ)<16384 by norm_num)
    hM hA hp hw hθ.le (cappedRepresentative_le_one _) hφ.le hσ
    (cappedRepresentative_le_one _) (by norm_num : (0:ℝ)≤16) hφθ hpP hwP
  have hg' : (I*p^2*ν^2*φ^2/θ^2)*(Real.sqrt I*R*ν*Real.sqrt (1+φ/σ)/θ^2)≤256*U := by
    convert hg using 1 <;> dsimp [I,R,ν,len,lam,U,L] <;> ring
  have hb'' : (I*p^2*ν^2*φ)*(Real.sqrt I*R*ν*Real.sqrt (1+φ/σ)/φ)≤U := by
    convert hb' using 1
    · dsimp [I,R,ν,len,lam]
      field_simp [hφ.ne']
    · dsimp [U,L]
      ring
  have hKg : 0≤Kg := relativeCauchyConstant_nonneg hCg
  have hKb : 0≤Kb := relativeCauchyConstant_nonneg hCb
  have hD : 0≤D := (dyadicBalanceConstant_pos (by norm_num) (by norm_num)).le
  have hr : Real.sqrt (256*U)=16*Real.sqrt U := by rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤256)]; norm_num
  apply hn.trans
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ Kg*D*Real.sqrt (256*U)+Kb*D*Real.sqrt U :=
      add_le_add (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hg') (mul_nonneg hKg hD))
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hb'') (mul_nonneg hKb hD))
    _ = _ := by rw [hr]; dsimp [Kg,Kb,D,U,E,L]; ring

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_RadialSummation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RVM

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff


lemma capped_large_magnetic_ennreal_sum {H p ν θ φ K : ℝ}
    (hH : 0<H) (hp : 0<p) (hν : 0≤ν) (hθ : 0<θ)
    (hνθ : ν≤θ) (hν1 : ν≤1) (hφ : 0≤φ) (hφ1 : φ≤1) (hK : 0≤K) :
    (∑'n : ℕ, ENNReal.ofReal (K*min
      (H*cappedRepresentative n*p^2*ν^2*φ)
      (Real.sqrt p*ν/(θ*Real.sqrt (H*cappedRepresentative n))))) ≤
      ENNReal.ofReal (K*dyadicBalanceConstant 1 (1/2)*p) := by
  let g : ℤ→ℝ := fun k=>min (H*(2:ℝ)^k*p^2) (Real.sqrt p/Real.sqrt (H*(2:ℝ)^k))
  have hg0 (k : ℤ) : 0≤g k := by dsimp [g]; positivity
  have hg := large_radius_magnetic_balance hH hp (by norm_num : (0:ℝ)<1)
    (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<1)
  simp only [min_self,one_pow,mul_one,one_mul,Real.one_rpow] at hg
  have he (n : ℕ) : cappedRepresentative n=(2:ℝ)^(-(n:ℤ)) := by
    simp only [cappedRepresentative,zpow_neg,zpow_natCast,inv_pow]
  have hinj : Function.Injective (fun n : ℕ=>-(n:ℤ)) := by
    intro a b hab
    exact_mod_cast neg_injective hab
  calc
    _ ≤ ∑'n : ℕ,ENNReal.ofReal (K*g (-(n:ℤ))) := by
      apply ENNReal.tsum_le_tsum
      intro n
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_left _ hK
      dsimp only [g]
      rw [←he]
      have hcn := (cappedRepresentative_pos n).le
      apply min_le_min
      · have hνsq : ν^2≤1 := by nlinarith only [hν,hν1]
        have hprod : ν^2*φ≤1 :=
          (mul_le_mul_of_nonneg_right hνsq hφ).trans (by simpa using hφ1)
        calc
          _ = (H*cappedRepresentative n*p^2)*(ν^2*φ) := by ring
          _ ≤ (H*cappedRepresentative n*p^2)*1 :=
            mul_le_mul_of_nonneg_left hprod (by positivity)
          _ = _ := mul_one _
      · have hr : 0<Real.sqrt (H*cappedRepresentative n) := Real.sqrt_pos.mpr (mul_pos hH (cappedRepresentative_pos _))
        apply (div_le_iff₀ (mul_pos hθ hr)).mpr
        calc
          Real.sqrt p*ν≤Real.sqrt p*θ := mul_le_mul_of_nonneg_left hνθ (Real.sqrt_nonneg _)
          _ = _ := by field_simp
    _ ≤ ∑'k : ℤ,ENNReal.ofReal (K*g k) :=
      ENNReal.tsum_comp_le_tsum_of_injective hinj (fun k=>ENNReal.ofReal (K*g k))
    _ = ENNReal.ofReal (K*∑'k : ℤ,g k) := by
      rw [←ENNReal.ofReal_tsum_of_nonneg (fun k=>mul_nonneg hK (hg0 k)) (hg.1.mul_left K),tsum_mul_left]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      simpa only [g,mul_assoc] using mul_le_mul_of_nonneg_left hg.2 hK

lemma remaining_good_coarse_balance {I p ν θ φ : ℝ}
    (hI : 0<I) (hI1 : I≤1) (hp : 0≤p) (hν : 0≤ν) (hθ : 0<θ)
    (hνθ : ν≤θ) (hθ1 : θ≤1) (hφ : 0≤φ) (hsector : φ≤16*θ) :
    Real.sqrt ((I*p^2*ν^2*φ^2/θ^2)*(Real.sqrt I*ν/θ^2)) ≤16*Real.sqrt I*p := by
  have hsqrt : Real.sqrt I≤1 := (Real.sqrt_le_one).mpr hI1
  have hν3 : ν^3≤θ^3 := pow_le_pow_left₀ hν hνθ 3
  have hφ2 : φ^2≤256*θ^2 := by nlinarith only [sq_nonneg (16*θ-φ),hsector,hφ,hθ]
  have hnum : ν^3*φ^2≤256*θ^4 := by
    calc
      _ ≤ θ^3*(256*θ^2) := mul_le_mul hν3 hφ2 (sq_nonneg _) (by positivity)
      _ = 256*θ^4*θ := by ring
      _ ≤ 256*θ^4*1 := mul_le_mul_of_nonneg_left hθ1 (by positivity)
      _ = _ := mul_one _
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity,?_⟩
  have hfactor : Real.sqrt I*(ν^3*φ^2)≤256*θ^4 := by
    calc
      _ ≤ 1*(256*θ^4) := mul_le_mul hsqrt hnum (by positivity) (by norm_num)
      _ = _ := one_mul _
  have he : (I*p^2*ν^2*φ^2/θ^2)*(Real.sqrt I*ν/θ^2)=
      (I*p^2)*(Real.sqrt I*(ν^3*φ^2))/θ^4 := by ring
  rw [he,show (16*Real.sqrt I*p)^2=256*I*p^2 by rw [mul_pow,mul_pow,Real.sq_sqrt hI.le]; ring]
  apply (div_le_iff₀ (pow_pos hθ 4)).mpr
  calc
    _ ≤ (I*p^2)*(256*θ^4) := mul_le_mul_of_nonneg_left hfactor (by positivity)
    _ = _ := by ring

lemma Admissible.direct_source_remaining_large_sum {d : Datum} (hd₀ : Admissible d) :
    ∃ Cg Cb : ℝ, 0 ≤ Cg ∧ 0 ≤ Cb ∧
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀ z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (S : Set Phase) (np nθ nφ j : ℕ) (a b I w : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → b-a ≤ I → 0 < I → I≤1 →
      cappedRepresentative nφ≤16*cappedRepresentative nθ →
      let p := sourceRepresentative np
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := fun nr=>relativeRepresentativeClosedBin T w ![np,nθ,nφ,nr] j
      let E := ∫x : Vec,totalEnergy s (0,x)
      let Kg := relativeCauchyConstant Cg E (20*E)
      let Kb := relativeCauchyConstant Cb E (120*E)
      (∑'nr : ℕ,if I ≤ max 1 T*cappedRepresentative nr then
        ∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V (B nr) z
          ∂physicalBinMeasure V (B nr) (Icc a b) else 0) ≤
      ENNReal.ofReal ((16*Kg*dyadicBalanceConstant (1/2) (1/2)+
        Kb*dyadicBalanceConstant 1 (1/2))*Real.sqrt I*p) := by
  obtain ⟨Cg,Cb,hCg,hCb,hsource⟩ := hd₀.direct_source_large_radius
  refine ⟨Cg,Cb,hCg,hCb,?_⟩
  intro s T F hs hT h0 zX S np nθ nφ j a b I w hS hS0 ha hb hJI hI hI1 hsector
  dsimp only
  let p := sourceRepresentative np
  let θ := cappedRepresentative nθ
  let φ := cappedRepresentative nφ
  let σ := cappedRepresentative j
  let ν := min θ σ
  let E := ∫x : Vec,totalEnergy s (0,x)
  let Kg := relativeCauchyConstant Cg E (20*E)
  let Kb := relativeCauchyConstant Cb E (120*E)
  let ag := I*p^2*ν^2*φ^2/θ^2
  let bg := Real.sqrt I*ν/θ^2
  let G := fun n=>ENNReal.ofReal (Kg*min (ag*Real.sqrt (max 1 T*cappedRepresentative n))
    (bg/Real.sqrt (max 1 T*cappedRepresentative n)))
  let Bm := fun n=>ENNReal.ofReal (Kb*Real.sqrt I*min
    (max 1 T*cappedRepresentative n*p^2*ν^2*φ)
    (Real.sqrt p*ν/(θ*Real.sqrt (max 1 T*cappedRepresentative n))))
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  have hθ : 0<θ := cappedRepresentative_pos _
  have hφ : 0<φ := cappedRepresentative_pos _
  have hν : 0<ν := lt_min hθ (cappedRepresentative_pos _)
  have hKg : 0≤Kg := relativeCauchyConstant_nonneg hCg
  have hKb : 0≤Kb := relativeCauchyConstant_nonneg hCb
  have hH : 0 < max 1 T := zero_lt_one.trans_le (le_max_left _ _)
  have hg := capped_sqrt_radius_ennreal_sum (show 0≤ag by dsimp [ag]; positivity)
    (show 0≤bg by dsimp [bg]; positivity) hH hKg
  have hm := capped_large_magnetic_ennreal_sum hH hp hν.le hθ (min_le_left _ _)
    ((min_le_left _ _).trans (cappedRepresentative_le_one _)) hφ.le
    (cappedRepresentative_le_one _) (mul_nonneg hKb (Real.sqrt_nonneg I))
  have hc := remaining_good_coarse_balance hI hI1 hp.le hν.le hθ (min_le_left _ _)
    (cappedRepresentative_le_one _) hφ.le hsector
  have hDs : 0≤dyadicBalanceConstant (1/2) (1/2) :=
    (dyadicBalanceConstant_pos (by norm_num) (by norm_num)).le
  have hDm : 0≤dyadicBalanceConstant 1 (1/2) :=
    (dyadicBalanceConstant_pos (by norm_num) (by norm_num)).le
  calc
    _ ≤ ∑'n : ℕ,(G n+Bm n) := by
      apply ENNReal.tsum_le_tsum
      intro n
      split_ifs with hIr
      · have h := hsource s T F hs hT h0 zX S ![np,nθ,nφ,n] j a b I w hS hS0 ha hb hJI hI hIr
        dsimp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,Matrix.cons_val,Fin.reduceFinMk] at h
        have hrad : 0 < max 1 T*cappedRepresentative n := mul_pos hH (cappedRepresentative_pos _)
        refine h.trans_eq ?_
        exact ENNReal.ofReal_add
          (mul_nonneg hKg (by positivity))
          (mul_nonneg (mul_nonneg hKb (Real.sqrt_nonneg I)) (le_min (by positivity) (by positivity)))
      · exact bot_le
    _ = (∑'n : ℕ,G n)+(∑'n : ℕ,Bm n) := ENNReal.tsum_add
    _ ≤ ENNReal.ofReal (Kg*dyadicBalanceConstant (1/2) (1/2)*Real.sqrt (ag*bg))+
        ENNReal.ofReal (Kb*Real.sqrt I*dyadicBalanceConstant 1 (1/2)*p) := add_le_add hg hm
    _ = ENNReal.ofReal (Kg*dyadicBalanceConstant (1/2) (1/2)*Real.sqrt (ag*bg)+
        Kb*Real.sqrt I*dyadicBalanceConstant 1 (1/2)*p) :=
      (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      calc
        _ ≤ Kg*dyadicBalanceConstant (1/2) (1/2)*(16*Real.sqrt I*p)+
            Kb*Real.sqrt I*dyadicBalanceConstant 1 (1/2)*p :=
          add_le_add (mul_le_mul_of_nonneg_left hc (mul_nonneg hKg hDs)) le_rfl
        _ = _ := by dsimp only [Kg,Kb,p,E]; ring

lemma shortSqrtConstant_pos : 0<(1-((2:ℝ)⁻¹)^(1/2:ℝ))⁻¹ := by
  apply inv_pos.mpr
  apply sub_pos.mpr
  exact Real.rpow_lt_one (by norm_num) (by norm_num) (by norm_num)

lemma relativeCauchyConstant_energy_le {C E Z : ℝ} (hC : 0≤C) (hE : 0≤E) (hZ : 0≤Z) :
    relativeCauchyConstant C E (Z*E) ≤ relativeCauchyConstant C 1 Z*(1+E) := by
  have hroot : Real.sqrt E≤1+E := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity,?_⟩
    nlinarith only [sq_nonneg E,hE]
  have he : relativeCauchyConstant C E (Z*E)=
      (31457280*C*Real.sqrt Z)*Real.sqrt E+
      (10240*Real.sqrt Z*Real.sqrt (62914560*C))*E := by
    unfold relativeCauchyConstant
    rw [Real.sqrt_mul hZ,Real.sqrt_mul (by positivity : 0≤62914560*C)]
    rw [show 10240*(Real.sqrt Z*Real.sqrt E)*(Real.sqrt (62914560*C)*Real.sqrt E)=
      (10240*Real.sqrt Z*Real.sqrt (62914560*C))*(Real.sqrt E)^2 by ring,Real.sq_sqrt hE]
    ring
  rw [he]
  have hE1 : E≤1+E := by linarith
  calc
    _ ≤ (31457280*C*Real.sqrt Z)*(1+E)+
        (10240*Real.sqrt Z*Real.sqrt (62914560*C))*(1+E) := add_le_add
      (mul_le_mul_of_nonneg_left hroot (by positivity))
      (mul_le_mul_of_nonneg_left hE1 (by positivity))
    _ = _ := by simp only [relativeCauchyConstant,mul_one]; ring

lemma remaining_stability_sqrt_coarse {M A w L : ℝ} (hM : 0<M) (hA : 0≤A)
    (hw : 0≤w) (hL : 1≤L) :
    Real.sqrt (32768*17*(1+16384*(M+Real.sqrt A))*w^2*Real.sqrt L) ≤
      (32768*17*16384)*(1+M+Real.sqrt A)*w*L := by
  let Z := (32768*17*16384)*(1+M+Real.sqrt A)
  have hsqrt : 0≤Real.sqrt A := by simpa only [Real.sqrt_zero] using Real.sqrt_le_sqrt hA
  have hZ : 1≤Z := by dsimp [Z]; nlinarith only [hM,hsqrt]
  have hcoeff : 32768*17*(1+16384*(M+Real.sqrt A))≤Z^2 := by
    have hb : 32768*17*(1+16384*(M+Real.sqrt A))≤Z := by dsimp [Z]; nlinarith
    exact hb.trans (by nlinarith only [hZ])
  have hroot : Real.sqrt L≤L^2 := by
    have h := (Real.sqrt_le_iff).mpr (And.intro (by linarith : 0≤L) (by nlinarith only [hL] : L≤L^2))
    exact h.trans (by nlinarith only [hL])
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity,?_⟩
  change _≤(Z*w*L)^2
  calc
    _ ≤ Z^2*w^2*L^2 := mul_le_mul
      (mul_le_mul_of_nonneg_right hcoeff (sq_nonneg w)) hroot (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by ring

lemma Admissible.direct_source_remaining_all_radii_oai {d : Datum} (hd₀ : Admissible d) :
    ∃ C : ℝ, 0≤C ∧
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀ z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (S : Set Phase) (np nθ nφ j : ℕ) (a b w M A P : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → a ≤ b → b-a ≤ (w/P)^2 →
      0 < M → 0 ≤ A → 1 ≤ P → 1 ≤ Real.log (2+P) → 0 < w → w≤P →
      sourceRepresentative np≤128*P →
      cappedRepresentative nφ≤16*cappedRepresentative nθ →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := fun nr=>relativeRepresentativeClosedBin T w ![np,nθ,nφ,nr] j
      let E := ∫x : Vec,totalEnergy s (0,x)
      (∑'nr : ℕ,∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V (B nr) z
        ∂physicalBinMeasure V (B nr) (Icc a b)) ≤
      ENNReal.ofReal (C*(1+E)*(1+M+Real.sqrt A)*w*Real.log (2+P)) := by
  obtain ⟨Cgs,Cbs,hCgs,hCbs,hshort⟩ := hd₀.direct_source_remaining_short_sum
  obtain ⟨Cgd,Cbd,hCgd,hCbd,hdef⟩ := hd₀.direct_source_deficit_short_sum
  obtain ⟨Cgl,Cbl,hCgl,hCbl,hlong⟩ := hd₀.direct_source_remaining_large_sum
  let Ds := dyadicBalanceConstant (1/2) (1/2)
  let Dm := dyadicBalanceConstant 1 (1/2)
  let Dn := (1-((2:ℝ)⁻¹)^(1/2:ℝ))⁻¹
  let gs := relativeCauchyConstant Cgs 1 20
  let bs := relativeCauchyConstant Cbs 1 120
  let gd := relativeCauchyConstant Cgd 1 20
  let bd := relativeCauchyConstant Cbd 1 120
  let gl := relativeCauchyConstant Cgl 1 20
  let bl := relativeCauchyConstant Cbl 1 120
  let Cs := (16*gs+bs)*Ds*(32768*17*16384)
  let Cd := (256*gd+bd)*16777216*Dn
  let Cl := (16*gl*Ds+bl*Dm)*128
  have hDs : 0≤Ds := (dyadicBalanceConstant_pos (by norm_num) (by norm_num)).le
  have hDm : 0≤Dm := (dyadicBalanceConstant_pos (by norm_num) (by norm_num)).le
  have hDn : 0≤Dn := shortSqrtConstant_pos.le
  have hgs : 0≤gs := relativeCauchyConstant_nonneg hCgs
  have hbs : 0≤bs := relativeCauchyConstant_nonneg hCbs
  have hgd : 0≤gd := relativeCauchyConstant_nonneg hCgd
  have hbd : 0≤bd := relativeCauchyConstant_nonneg hCbd
  have hgl : 0≤gl := relativeCauchyConstant_nonneg hCgl
  have hbl : 0≤bl := relativeCauchyConstant_nonneg hCbl
  have hCs : 0≤Cs := by dsimp only [Cs]; positivity
  have hCd : 0≤Cd := by dsimp only [Cd]; positivity
  have hCl : 0≤Cl := by dsimp only [Cl]; positivity
  refine ⟨Cs+Cd+Cl,by positivity,?_⟩
  intro s T F hs hT h0 zX S np nθ nφ j a b w M A P hS hS0 ha hb hab hJI
    hM hA hP1 hL hw hwP hpP hsector HX HZ
  dsimp only
  let I := (w/P)^2
  let L := Real.log (2+P)
  let E := ∫x : Vec,totalEnergy s (0,x)
  let p := sourceRepresentative np
  let θ := cappedRepresentative nθ
  let φ := cappedRepresentative nφ
  let σ := cappedRepresentative j
  let B := fun nr=>relativeRepresentativeClosedBin T w ![np,nθ,nφ,nr] j
  let J : ℕ→ℝ≥0∞ := fun nr=>∫⁻z : ConeCoordinate,
    physicalDirectSourceDensity s (fun t=>(prefixFlow F.flow T zX t).1)
      (fun t=>(prefixFlow F.flow T zX t).2) (B nr) z
      ∂physicalBinMeasure (fun t=>(prefixFlow F.flow T zX t).2) (B nr) (Icc a b)
  let Jshort : ℕ→ℝ≥0∞ := fun nr=>if max 1 T*cappedRepresentative nr≤I then J nr else 0
  let Jlong : ℕ→ℝ≥0∞ := fun nr=>if I ≤ max 1 T*cappedRepresentative nr then J nr else 0
  let U := (1+E)*(1+M+Real.sqrt A)*w*L
  have hP : 0<P := zero_lt_one.trans_le hP1
  have hI : 0<I := sq_pos_of_pos (div_pos hw hP)
  have hI1 : I≤1 := by dsimp only [I]; exact pow_le_one₀ (div_pos hw hP).le ((div_le_one hP).mpr hwP)
  have hp : 0<p := by dsimp only [p,sourceRepresentative]; positivity
  have hE : 0≤E := integral_nonneg (hs.total_energy_nonneg ⟨le_rfl,hT⟩)
  have hL0 : 0≤L := zero_le_one.trans hL
  have hU : 0≤U := by dsimp only [U]; positivity
  have hMA : 1≤1+M+Real.sqrt A := by linarith [Real.sqrt_nonneg A]
  have hbaseU : (1+E)*w≤U := by
    calc
      _ = (1+E)*1*w*1 := by ring
      _ ≤ (1+E)*(1+M+Real.sqrt A)*w*L := by gcongr
  have hIsqrt : Real.sqrt I=w/P := Real.sqrt_sq (div_pos hw hP).le
  have hIw : Real.sqrt I≤w := by rw [hIsqrt]; exact (div_le_self hw.le hP1)
  have hgse := relativeCauchyConstant_energy_le hCgs hE (by norm_num : (0:ℝ)≤20)
  have hbse := relativeCauchyConstant_energy_le hCbs hE (by norm_num : (0:ℝ)≤120)
  have hgde := relativeCauchyConstant_energy_le hCgd hE (by norm_num : (0:ℝ)≤20)
  have hbde := relativeCauchyConstant_energy_le hCbd hE (by norm_num : (0:ℝ)≤120)
  have hgle := relativeCauchyConstant_energy_le hCgl hE (by norm_num : (0:ℝ)≤20)
  have hble := relativeCauchyConstant_energy_le hCbl hE (by norm_num : (0:ℝ)≤120)
  have hshortBound : (∑'n,Jshort n)≤ENNReal.ofReal ((Cs+Cd)*U) := by
    by_cases hdeficit : σ*p≤512 ∨ σ*w≤32
    · have hn := hdef s T F hs hT h0 zX S np nθ nφ j a b I w P hS hS0 ha hb hJI
        hI hI1 hw hP hpP le_rfl hsector hdeficit
      apply hn.trans
      apply ENNReal.ofReal_le_ofReal
      calc
        _ ≤ ((256*(gd*(1+E))+bd*(1+E))*16777216*Dn)*w := by
          dsimp only [Dn,gd,bd]
          gcongr
        _ = Cd*((1+E)*w) := by dsimp only [Cd]; ring
        _ ≤ Cd*U := mul_le_mul_of_nonneg_left hbaseU hCd
        _ ≤ (Cs+Cd)*U := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCs) hU
    · have hh := not_or.mp hdeficit
      have hn := hshort s T F hs hT h0 zX S np nθ nφ j a b w M A P hS hS0 ha hb hab hJI
        hM hA hP hL hw hwP hpP hsector (le_of_lt (lt_of_not_ge hh.1)) (le_of_lt (lt_of_not_ge hh.2)) HX HZ
      have hc := remaining_stability_sqrt_coarse hM hA hw.le hL
      apply hn.trans
      apply ENNReal.ofReal_le_ofReal
      calc
        _ ≤ (16*(gs*(1+E))+bs*(1+E))*Ds*
            ((32768*17*16384)*(1+M+Real.sqrt A)*w*L) := by
          dsimp only [gs,bs,Ds,L]
          gcongr
        _ = Cs*U := by dsimp only [Cs,U]; ring
        _ ≤ (Cs+Cd)*U := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCd) hU
  have hlongBound : (∑'n,Jlong n)≤ENNReal.ofReal (Cl*U) := by
    have hn := hlong s T F hs hT h0 zX S np nθ nφ j a b I w hS hS0 ha hb hJI hI hI1 hsector
    apply hn.trans
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ (16*(gl*(1+E))*Ds+(bl*(1+E))*Dm)*Real.sqrt I*(128*P) := by
        dsimp only [gl,bl,Ds,Dm]
        gcongr
      _ = Cl*((1+E)*w) := by rw [hIsqrt]; dsimp only [Cl]; field_simp
      _ ≤ Cl*U := mul_le_mul_of_nonneg_left hbaseU hCl
  calc
    _ = ∑'n,J n := rfl
    _ ≤ ∑'n,(Jshort n+Jlong n) := by
      apply ENNReal.tsum_le_tsum
      intro n
      dsimp only [Jshort,Jlong]
      by_cases hrI : max 1 T*cappedRepresentative n≤I
      · rw [ite_eq_left hrI]
        exact le_add_of_nonneg_right (bot_le : (0 : ℝ≥0∞) ≤ _)
      · rw [ite_eq_right hrI,ite_eq_left (le_of_lt (lt_of_not_ge hrI)),zero_add]
    _ = (∑'n,Jshort n)+(∑'n,Jlong n) := ENNReal.tsum_add
    _ ≤ ENNReal.ofReal ((Cs+Cd)*U)+ENNReal.ofReal (Cl*U) := add_le_add hshortBound hlongBound
    _ = _ := by
      rw [←ENNReal.ofReal_add (mul_nonneg (add_nonneg hCs hCd) hU) (mul_nonneg hCl hU)]
      congr 1
      dsimp only [U,E,L]
      ring



open Set Filter Metric MeasureTheory _root_.Classical
open scoped ENNReal Topology ContDiff



open Set Filter Metric MeasureTheory _root_.Classical
open scoped ENNReal Topology ContDiff


end RVM

end

end OAI
end

theorem solution : type_of% @OAI.RVM.Admissible.direct_source_remaining_all_radii_oai := @OAI.RVM.Admissible.direct_source_remaining_all_radii_oai
