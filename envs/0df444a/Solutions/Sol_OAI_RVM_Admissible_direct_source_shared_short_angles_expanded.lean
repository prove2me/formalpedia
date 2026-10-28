-- Prove2me | solution 1 for OAI.RVM.Admissible.direct_source_shared_short_angles_expanded
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:46:05.69379+00:00
-- url     : https://prove2.me/submissions/ec000d78-53e4-4307-aef7-11de7a68a9e4

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000
import Theorems.Thm_OAI_RVM_Admissible_direct_source_relative_budget
import Theorems.Thm_OAI_RVM_EnergyPrefix_goodFieldBudget_finite
import Theorems.Thm_OAI_RVM_EnergyPrefix_shared_magneticFieldBudget
import Theorems.Thm_OAI_RVM_remaining_stable_source_angular

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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Continuation_PrefixParticle
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
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff NNReal ENNReal
open scoped Topology ContDiff
open Set
open scoped Topology ContDiff RealInnerProductSpace
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal

namespace RVM

lemma dyadicWindow_one_sqrt {D : ℝ} (j : ℕ)
    (hlo : ((2:ℝ)^j)⁻¹^2/2≤D) (hhi : D≤8*((2:ℝ)^j)⁻¹^2) :
    DyadicWindow 1 j (Real.sqrt (D/2)) := by
  have hp : 0<(2:ℝ)^j := by positivity
  have hi : 0<((2:ℝ)^j)⁻¹ := inv_pos.mpr hp
  have hD0 : 0≤D := (by positivity : 0≤((2:ℝ)^j)⁻¹^2/2).trans hlo
  have hD : 0≤D/2 := by positivity
  have hsq := Real.sq_sqrt hD
  have hlo' : ((2:ℝ)^j)⁻¹/2≤Real.sqrt (D/2) := by
    nlinarith [Real.sqrt_nonneg (D/2)]
  have hhi' : Real.sqrt (D/2)≤2*((2:ℝ)^j)⁻¹ := by
    nlinarith [Real.sqrt_nonneg (D/2)]
  constructor
  · have hh := mul_le_mul_of_nonneg_left hlo' hp.le
    simpa only [pow_one,← mul_div_assoc,mul_inv_cancel₀ hp.ne'] using hh
  · have hh := mul_le_mul_of_nonneg_left hhi' hp.le
    simpa only [pow_one,mul_left_comm,mul_inv_cancel₀ hp.ne',mul_one] using hh

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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_PhysicalProjectedRemainderDensity
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

lemma magneticFieldBudget_mono (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase)
    (T : ℝ) (k j : ℕ) (I : ℝ) {a b lo hi : ℝ} (hsub : Icc a b⊆Icc lo hi) :
    magneticFieldBudget s α zX T k a b I j ≤ magneticFieldBudget s α zX T k lo hi I j := by
  exact mul_le_mul' le_rfl (lintegral_mono_set hsub)

lemma radial_source_interval_common {T a b R : ℝ} {C : ClosedConeBin}
    (hmin : 0≤C.rmin) (hmax : C.rmax≤R) :
    Icc (max 0 (a-C.rmax)) (min T (b-C.rmin))⊆Icc (max 0 (a-R)) (min T b) := by
  intro σ hσ
  constructor
  · exact (max_le_max le_rfl (sub_le_sub_left hmax a)).trans hσ.1
  · exact hσ.2.trans (min_le_min le_rfl (by linarith))

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

lemma source_far_sqrt_mass {b p θ R r φ : ℝ}
    (hb : 0≤b) (hp : 0<p) (hθ : 0<θ) (hR : 0≤R) (hr : 0 < r) (hφ : 0<φ) :
    Real.sqrt (b*p^2*θ^2*R^2/(r*φ^2)) =
      Real.sqrt b*p*θ*R/(Real.sqrt r*φ) := by
  rw [Real.sqrt_div (by positivity),Real.sqrt_mul (by positivity : 0≤b*p^2*θ^2),
    Real.sqrt_mul (by positivity : 0≤b*p^2),Real.sqrt_mul hb,
    Real.sqrt_mul hr.le,Real.sqrt_sq hp.le,Real.sqrt_sq hθ.le,
    Real.sqrt_sq hR,Real.sqrt_sq hφ.le]

lemma ennreal_half_ofReal {x : ℝ} (hx : 0≤x) :
    (ENNReal.ofReal x)^(1/2:ℝ)=ENNReal.ofReal (Real.sqrt x) := by
  rw [Real.sqrt_eq_rpow,ENNReal.ofReal_rpow_of_nonneg hx (by norm_num)]

end RVM

end

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

namespace RVM

lemma Admissible.direct_source_shared_radius_budget {d : Datum} (hd₀ : Admissible d) :
    ∃ Cg Cb : ℝ, 0 ≤ Cg ∧ 0 ≤ Cb ∧
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀ z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (S : Set Phase) (k : Fin 4→ℕ) (j : ℕ)
      (a b I len w M A P L massScale Cs : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → a ≤ b → 0 < len → len ≤ I → b-a ≤ I →
      0 < M → 0 ≤ A → 0 < P → 0 ≤ L → 0 < massScale → 0 < w → 128 ≤ Cs →
      massScale ≤ sourceRepresentative (k 0)/128 → massScale ≤ w/8 →
      512 ≤ cappedRepresentative j*sourceRepresentative (k 0) →
      32 ≤ cappedRepresentative j*w →
      2*len ≤ (Cs*(P/massScale)*(M/cappedRepresentative j+
        Real.sqrt (A*L/cappedRepresentative j)))⁻¹^2 →
      max 1 T*cappedRepresentative (k 3)≤I →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P L →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P L) →
      let p := sourceRepresentative (k 0)
      let θ := cappedRepresentative (k 1)
      let φ := cappedRepresentative (k 2)
      let σ := cappedRepresentative j
      let r := max 1 T*cappedRepresentative (k 3)
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := relativeRepresentativeClosedBin T w k j
      let E := ∫x : Vec,totalEnergy s (0,x)
      let G := goodFieldBudget s X (fun t=>velocity (V t)) 1 a b I (k 2)
      let Hf := magneticFieldBudget s F.flow zX T 1 (max 0 (a-2*I)) (min T b) I (k 2)
      let O := ENNReal.ofReal (491520*E*(1+φ/σ)*(1+I/len)/(p*r*φ^2))
      let H := ENNReal.ofReal (576*I*r*φ^2)
      let Dg := ENNReal.ofReal (128*Cg*p^3*(min θ σ)^2)
      let Db := ENNReal.ofReal (128*Cb*p^3*(min θ σ)^2)
      (∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V B z
        ∂physicalBinMeasure V B (Icc a b)) ≤
      ENNReal.ofReal (10240*φ/(p*θ^2))*
        ((ENNReal.ofReal I*G)^(1/2:ℝ)*(min (Dg^2*H) (Dg*O))^(1/2:ℝ))+
      ENNReal.ofReal (10240/p)*
        ((ENNReal.ofReal (2*I)*Hf)^(1/2:ℝ)*(min (Db^2*H) (Db*O))^(1/2:ℝ)) := by
  obtain ⟨Cg,Cb,hCg,hCb,hsource⟩ := hd₀.direct_source_relative_budget
  refine ⟨Cg,Cb,hCg,hCb,?_⟩
  intro s T F hs hT h0 zX S k j a b I len w M A P L massScale Cs hS hS0
    ha hb hab hlen hlenI hJI hM hA hP hL hm hw hCs hmq hmw hqσ hwσ hstable hrI HX HZ
  dsimp only
  let p := sourceRepresentative (k 0)
  let θ := cappedRepresentative (k 1)
  let φ := cappedRepresentative (k 2)
  let σ := cappedRepresentative j
  let r := max 1 T*cappedRepresentative (k 3)
  let B := relativeRepresentativeClosedBin T w k j
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  let E := ∫x : Vec,totalEnergy s (0,x)
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  have hθ : 0<θ := cappedRepresentative_pos _
  have hφ : 0<φ := cappedRepresentative_pos _
  have hσ : 0<σ := cappedRepresentative_pos _
  have hr : 0 < r := mul_pos (zero_lt_one.trans_le (le_max_left _ _)) (cappedRepresentative_pos _)
  have hBmax : B.rmax=2*r := by dsimp [B,relativeRepresentativeClosedBin,representativeClosedBin,r]; ring
  have hBmin : B.rmin=r/2 := rfl
  have hBDmin : B.Dmin=φ^2/2 := rfl
  have hI : 0<I := hlen.trans_le hlenI
  have hE : 0≤E := integral_nonneg (hs.total_energy_nonneg ⟨le_rfl,hT⟩)
  have hJ : Icc a b⊆Icc 0 T := Icc_subset_Icc ha hb
  have hangle (D : ℝ) (hD : D∈Icc B.Dmin B.Dmax) : DyadicWindow 1 (k 2) (Real.sqrt (D/2)) :=
    dyadicWindow_one_sqrt (k 2)
      (by simpa only [B,relativeRepresentativeClosedBin,representativeClosedBin,cappedRepresentative,inv_pow] using hD.1)
      (by simpa only [B,relativeRepresentativeClosedBin,representativeClosedBin,cappedRepresentative,inv_pow] using hD.2)
  have hn := hsource s T F hs hT h0 zX B S M A P L a b massScale φ θ σ Cs p len I 1 (k 2)
    hS hS0 ha hb hab hp hlen hlenI hJI hM hA hP hL hm hφ hθ hσ
    (cappedRepresentative_le_one _) hCs hstable le_rfl le_rfl hmq hmw
    (by rw [hBmin]; positivity) (by rw [hBmax]; positivity) (by rw [hBDmin]; positivity)
    le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl
    (by change 4≤σ*(p/128); dsimp [σ,p] at *; nlinarith only [hqσ])
    (by change 4≤σ*(w/8); dsimp [σ] at *; nlinarith only [hwσ]) hangle HX HZ
  dsimp only at hn
  have hmass : (ENNReal.ofReal (30720*B.rmax/p*(1+φ/σ)*(1+I/len))*ENNReal.ofReal E)/
      ENNReal.ofReal (B.rmin^2*B.Dmin) =
      ENNReal.ofReal (491520*E*(1+φ/σ)*(1+I/len)/(p*r*φ^2)) := by
    rw [hBmax,hBmin,hBDmin,←ENNReal.ofReal_mul (by positivity : 0≤30720*(2*r)/p*(1+φ/σ)*(1+I/len)),
      ←ENNReal.ofReal_div_of_pos (by positivity : 0<(r/2)^2*(φ^2/2))]
    congr 1
    field_simp [hp.ne',hr.ne',hφ.ne',hσ.ne',hlen.ne']
    ring
  have hvolume : volume (Icc a b)*ENNReal.ofReal (B.rmax-B.rmin)*ENNReal.ofReal (384*φ^2) ≤
      ENNReal.ofReal (576*I*r*φ^2) := by
    rw [Real.volume_Icc,hBmax,hBmin]
    calc
      _ ≤ ENNReal.ofReal I*ENNReal.ofReal (2*r-r/2)*ENNReal.ofReal (384*φ^2) := by gcongr
      _ = _ := by
        rw [←ENNReal.ofReal_mul hI.le,←ENNReal.ofReal_mul (mul_nonneg hI.le (by linarith : 0≤2*r-r/2))]
        congr 1
        ring
  have hmag : magneticFieldBudget s F.flow zX T 1
      (max 0 (a-B.rmax)) (min T (b-B.rmin)) I (k 2) ≤
      magneticFieldBudget s F.flow zX T 1 (max 0 (a-2*I)) (min T b) I (k 2) := by
    apply magneticFieldBudget_mono
    apply radial_source_interval_common
    · rw [hBmin]; positivity
    · rw [hBmax]
      exact mul_le_mul_of_nonneg_left hrI (by norm_num)
  have heG : 80*φ/(p/128*θ^2)=10240*φ/(p*θ^2) := by ring
  have heB : 80/(p/128)=10240/p := by ring
  rw [heG,heB,hmass] at hn
  apply hn.trans
  apply add_le_add
  · apply mul_le_mul' le_rfl
    apply mul_le_mul' le_rfl
    apply ENNReal.rpow_le_rpow _ (by norm_num)
    exact min_le_min (mul_le_mul' le_rfl hvolume) le_rfl
  · apply mul_le_mul' le_rfl
    apply mul_le_mul' (ENNReal.rpow_le_rpow (mul_le_mul' le_rfl hmag) (by norm_num))
    apply ENNReal.rpow_le_rpow _ (by norm_num)
    exact min_le_min (mul_le_mul' le_rfl hvolume) le_rfl

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

lemma relative_density_near_sqrt {C I p ν r φ : ℝ}
    (hC : 0≤C) (hI : 0≤I) (hp : 0≤p) (_hν : 0≤ν) (hr : 0 ≤ r) (hφ : 0≤φ) :
    Real.sqrt ((128*C*p^3*ν^2)^2*(576*I*r*φ^2)) =
      3072*C*p^3*ν^2*Real.sqrt I*Real.sqrt r*φ := by
  rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (by positivity),
    show 576*I*r*φ^2=576*((I*r)*φ^2) by ring,
    Real.sqrt_mul (by norm_num : (0:ℝ)≤576),Real.sqrt_mul (mul_nonneg hI hr),
    Real.sqrt_mul hI,Real.sqrt_sq hφ]
  norm_num
  ring

lemma relative_density_far_sqrt {C E p ν R r φ κ : ℝ}
    (hC : 0≤C) (hE : 0≤E) (hp : 0<p) (hν : 0<ν) (hR : 0≤R)
    (hr : 0 < r) (hφ : 0<φ) (hκ : 0≤κ) :
    Real.sqrt ((128*C*p^3*ν^2)*(491520*E*κ*R^2/(p*r*φ^2))) =
      Real.sqrt (62914560*C*E)*Real.sqrt κ*p*ν*R/(Real.sqrt r*φ) := by
  have he : (128*C*p^3*ν^2)*(491520*E*κ*R^2/(p*r*φ^2))=
      (62914560*C*E*κ)*p^2*ν^2*R^2/(r*φ^2) := by
    field_simp [hp.ne',hr.ne',hφ.ne']
    ring
  rw [he,source_far_sqrt_mass (by positivity) hp hν hR hr hφ,
    Real.sqrt_mul (by positivity : 0≤62914560*C*E)]

lemma relative_radius_cauchy_scalar {C E Z I p ν R r φ κ γ : ℝ}
    (hC : 0≤C) (hE : 0≤E) (hZ : 0≤Z) (hI : 0<I) (hp : 0<p)
    (hν : 0<ν) (hR : 0≤R) (hr : 0 < r) (hφ : 0<φ) (hκ : 0≤κ) (hγ : 0≤γ) :
    let D := ENNReal.ofReal (128*C*p^3*ν^2)
    let H := ENNReal.ofReal (576*I*r*φ^2)
    let O := ENNReal.ofReal (491520*E*κ*R^2/(p*r*φ^2))
    ENNReal.ofReal (10240*γ/p)*
      ((ENNReal.ofReal (Z*I))^(1/2:ℝ)*(min (D^2*H) (D*O))^(1/2:ℝ)) ≤
    ENNReal.ofReal (relativeCauchyConstant C E Z*
      min ((I*p^2*ν^2*φ*γ)*Real.sqrt r)
        ((Real.sqrt I*R*ν*Real.sqrt κ*γ/φ)/Real.sqrt r)) := by
  dsimp only
  let K := relativeCauchyConstant C E Z
  have hK : 0≤K := relativeCauchyConstant_nonneg hC
  rw [mul_min_of_nonneg _ _ hK,ENNReal.ofReal_min]
  apply le_min
  · calc
      _ ≤ ENNReal.ofReal (10240*γ/p)*
          ((ENNReal.ofReal (Z*I))^(1/2:ℝ)*
            ((ENNReal.ofReal (128*C*p^3*ν^2))^2*ENNReal.ofReal (576*I*r*φ^2))^(1/2:ℝ)) := by
        gcongr
        exact min_le_left _ _
      _ = ENNReal.ofReal ((31457280*C*Real.sqrt Z)*
          ((I*p^2*ν^2*φ*γ)*Real.sqrt r)) := by
        rw [←ENNReal.ofReal_pow (by positivity : 0≤128*C*p^3*ν^2),
          ←ENNReal.ofReal_mul (sq_nonneg _),
          ennreal_half_ofReal (by positivity),ennreal_half_ofReal (by positivity),
          relative_density_near_sqrt hC hI.le hp.le hν.le hr.le hφ.le,
          Real.sqrt_mul hZ,
          ←ENNReal.ofReal_mul (by positivity : 0≤Real.sqrt Z*Real.sqrt I),
          ←ENNReal.ofReal_mul (by positivity : 0≤10240*γ/p)]
        congr 1
        have hIsq : Real.sqrt I*Real.sqrt I=I := Real.mul_self_sqrt hI.le
        calc
          _ = 31457280*C*Real.sqrt Z*(Real.sqrt I*Real.sqrt I)*p^2*ν^2*φ*γ*Real.sqrt r := by
            field_simp [hp.ne']
            ring
          _ = _ := by rw [hIsq]; ring
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact le_add_of_nonneg_right (by positivity)
  · calc
      _ ≤ ENNReal.ofReal (10240*γ/p)*
          ((ENNReal.ofReal (Z*I))^(1/2:ℝ)*
            ((ENNReal.ofReal (128*C*p^3*ν^2))*
              ENNReal.ofReal (491520*E*κ*R^2/(p*r*φ^2)))^(1/2:ℝ)) := by
        gcongr
        exact min_le_right _ _
      _ = ENNReal.ofReal ((10240*Real.sqrt Z*Real.sqrt (62914560*C*E))*
          ((Real.sqrt I*R*ν*Real.sqrt κ*γ/φ)/Real.sqrt r)) := by
        rw [←ENNReal.ofReal_mul (by positivity : 0≤128*C*p^3*ν^2),
          ennreal_half_ofReal (by positivity),ennreal_half_ofReal (by positivity),
          relative_density_far_sqrt hC hE hp hν hR hr hφ hκ,Real.sqrt_mul hZ,
          ←ENNReal.ofReal_mul (by positivity : 0≤Real.sqrt Z*Real.sqrt I),
          ←ENNReal.ofReal_mul (by positivity : 0≤10240*γ/p)]
        congr 1
        field_simp [hp.ne',hφ.ne',(Real.sqrt_pos.mpr hr).ne']
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact le_add_of_nonneg_left (by positivity)

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

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_TransportRemainder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RVM

section
open Set Filter Metric MeasureTheory _root_.Classical
open scoped ENNReal Topology ContDiff


lemma relativeSourceAngle_nonneg {θ φ σ : ℝ} (hθ : 0≤θ) (hφ : 0≤φ) (hσ : 0<σ) :
    0 ≤ relativeSourceAngle θ φ σ := by
  dsimp [relativeSourceAngle]
  positivity

lemma Admissible.direct_source_shared_short_angles_expanded_oai {d : Datum} (hd₀ : Admissible d) :
    ∃ Cg Cb : ℝ, 0≤Cg ∧ 0≤Cb ∧
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0≤T → (∀z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (S : Set Phase) (np nφ : ℕ) (a b I w M A P : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0≤a → b≤T → a≤b → 0<I → b-a≤I → 0<M → 0≤A → 0<P → 0<w →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
    ∀ (Sθ : Finset ℕ) (Sσ : ℕ→Finset ℕ),
      (∀i∈Sθ,cappedRepresentative nφ≤16384*cappedRepresentative i) →
      (∀i∈Sθ,∀j∈Sσ i,cappedRepresentative j≤131080*cappedRepresentative i ∧
        512 ≤ cappedRepresentative j*sourceRepresentative np ∧ 32 ≤ cappedRepresentative j*w) →
      let p := sourceRepresentative np
      let φ := cappedRepresentative nφ
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := fun i j nr=>relativeRepresentativeClosedBin T w ![np,i,nφ,nr] j
      let E := ∫x : Vec,totalEnergy s (0,x)
      let Kg := relativeCauchyConstant Cg E
        (goodFieldBudget s X (fun t=>velocity (V t)) 1 a b I nφ).toReal
      let Kb := relativeCauchyConstant Cb E
        (2*(magneticFieldBudget s F.flow zX T 1 (max 0 (a-2*I)) (min T b) I nφ).toReal)
      let D := dyadicBalanceConstant (1/2) (1/2)
      let R₁ := 2*Real.sqrt 16384*(I : ℝ)^(1/4:ℝ)*Real.sqrt (P/min p w)*
        (Real.sqrt M+Real.sqrt (Real.sqrt (A*Real.log (2+P))))
      (∑i∈Sθ,∑j∈Sσ i,∑'nr : ℕ,if max 1 T*cappedRepresentative nr≤I then
        ∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V (B i j nr) z
          ∂physicalBinMeasure V (B i j nr) (Icc a b) else 0) ≤
      ENNReal.ofReal (D*(I : ℝ)^(3/4:ℝ)*p*
        (Kg*(2*remainingGoodConstant 131080 16384 0*Real.sqrt φ+R₁*remainingGoodConstant 131080 16384 (1/2))+
         Kb*(2*remainingMagneticConstant 131080 16384 0+R₁*remainingMagneticConstant 131080 16384 (1/2)))) := by
  have hshortRadius :
      ∃ Cg Cb : ℝ, 0 ≤ Cg ∧ 0 ≤ Cb ∧
      ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
        EnergyPrefix s T → 0 ≤ T → (∀ z,s.f (0,z)=d.f₀ z) →
      ∀ (zX : Phase) (S : Set Phase) (k : Fin 4→ℕ) (j : ℕ)
        (a b I len w M A P L massScale Cs : ℝ),
        IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
        0 ≤ a → b ≤ T → a ≤ b → 0 < len → len ≤ I → b-a ≤ I →
        0 < M → 0 ≤ A → 0 < P → 0 ≤ L → 0 < massScale → 0 < w → 128 ≤ Cs →
        massScale ≤ sourceRepresentative (k 0)/128 → massScale ≤ w/8 →
        512 ≤ cappedRepresentative j*sourceRepresentative (k 0) →
        32 ≤ cappedRepresentative j*w →
        2*len ≤ (Cs*(P/massScale)*(M/cappedRepresentative j+
          Real.sqrt (A*L/cappedRepresentative j)))⁻¹^2 →
        max 1 T*cappedRepresentative (k 3) ≤ I →
        IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P L →
        (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P L) →
        let p := sourceRepresentative (k 0)
        let θ := cappedRepresentative (k 1)
        let φ := cappedRepresentative (k 2)
        let σ := cappedRepresentative j
        let r := max 1 T*cappedRepresentative (k 3)
        let X := fun t=>(prefixFlow F.flow T zX t).1
        let V := fun t=>(prefixFlow F.flow T zX t).2
        let B := relativeRepresentativeClosedBin T w k j
        let E := ∫x : Vec,totalEnergy s (0,x)
        let R := Real.sqrt (1+I/len)
        let ν := min θ σ
        let κ := 1+φ/σ
        let G := (goodFieldBudget s X (fun t=>velocity (V t)) 1 a b I (k 2)).toReal
        let Hf := (magneticFieldBudget s F.flow zX T 1 (max 0 (a-2*I)) (min T b) I (k 2)).toReal
        let Kg := relativeCauchyConstant Cg E G
        let Kb := relativeCauchyConstant Cb E (2*Hf)
        (∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V B z
          ∂physicalBinMeasure V B (Icc a b)) ≤
        ENNReal.ofReal (Kg*min ((I*p^2*ν^2*φ^2/θ^2)*Real.sqrt r)
          ((Real.sqrt I*R*ν*Real.sqrt κ/θ^2)/Real.sqrt r)+
        Kb*min ((I*p^2*ν^2*φ)*Real.sqrt r)
          ((Real.sqrt I*R*ν*Real.sqrt κ/φ)/Real.sqrt r)) := by
    obtain ⟨Cg,Cb,hCg,hCb,hsource⟩ := hd₀.direct_source_shared_radius_budget
    refine ⟨Cg,Cb,hCg,hCb,?_⟩
    intro s T F hs hT h0 zX S k j a b I len w M A P L massScale Cs hS hS0
      ha hb hab hlen hlenI hJI hM hA hP hL hm hw hCs hmq hmw hqσ hwσ hstable hrI HX HZ
    have hn := hsource s T F hs hT h0 zX S k j a b I len w M A P L massScale Cs
      hS hS0 ha hb hab hlen hlenI hJI hM hA hP hL hm hw hCs hmq hmw hqσ hwσ hstable hrI HX HZ
    dsimp only at hn ⊢
    let p := sourceRepresentative (k 0)
    let θ := cappedRepresentative (k 1)
    let φ := cappedRepresentative (k 2)
    let σ := cappedRepresentative j
    let r := max 1 T*cappedRepresentative (k 3)
    let ν := min θ σ
    let κ := 1+φ/σ
    let E := ∫x : Vec,totalEnergy s (0,x)
    let R := Real.sqrt (1+I/len)
    have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
    have hθ : 0<θ := cappedRepresentative_pos _
    have hφ : 0<φ := cappedRepresentative_pos _
    have hσ : 0<σ := cappedRepresentative_pos _
    have hν : 0<ν := lt_min hθ hσ
    have hκ : 0≤κ := by dsimp [κ]; positivity
    have hr : 0 < r := mul_pos (zero_lt_one.trans_le (le_max_left _ _)) (cappedRepresentative_pos _)
    have hI : 0<I := hlen.trans_le hlenI
    have hE : 0≤E := integral_nonneg (hs.total_energy_nonneg ⟨le_rfl,hT⟩)
    have hR : 0≤R := Real.sqrt_nonneg _
    have hRsq : R^2=1+I/len := Real.sq_sqrt (by positivity)
    let X := fun t=>(prefixFlow F.flow T zX t).1
    let V := fun t=>(prefixFlow F.flow T zX t).2
    let G := goodFieldBudget s X (fun t=>velocity (V t)) 1 a b I (k 2)
    let Hf := magneticFieldBudget s F.flow zX T 1 (max 0 (a-2*I)) (min T b) I (k 2)
    have hG : G≠⊤ := ne_top_of_le_ne_top
      (hs.goodFieldBudget_finite X (fun t=>velocity (V t)) 1 (Icc_subset_Icc ha hb) hI)
      (ENNReal.le_tsum (f := fun index=>goodFieldBudget s X (fun t=>velocity (V t)) 1 a b I index) (k 2))
    have hF : Hf≠⊤ := by
      apply ne_top_of_le_ne_top _ ((ENNReal.le_tsum (k 2)).trans
        (hs.shared_magneticFieldBudget F.flow zX 1 hI (by norm_num : (0:ℝ)≤2) hJI))
      finiteness
    have hGe : ENNReal.ofReal (G.toReal*I)=ENNReal.ofReal I*G := by
      rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,ENNReal.ofReal_toReal hG,mul_comm]
    have hFe : ENNReal.ofReal ((2*Hf.toReal)*I)=ENNReal.ofReal (2*I)*Hf := by
      rw [show (2*Hf.toReal)*I=(2*I)*Hf.toReal by ring,
        ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_toReal hF]
    have hg := relative_radius_cauchy_scalar hCg hE ENNReal.toReal_nonneg hI hp hν hR hr hφ hκ
      (show 0≤φ/θ^2 by positivity) (Z:=G.toReal)
    dsimp only at hg
    have heγ : 10240*(φ/θ^2)/p=10240*φ/(p*θ^2) := by ring
    have hea : I*p^2*ν^2*φ*(φ/θ^2)=I*p^2*ν^2*φ^2/θ^2 := by ring
    have heb : Real.sqrt I*R*ν*Real.sqrt κ*(φ/θ^2)/φ=Real.sqrt I*R*ν*Real.sqrt κ/θ^2 := by
      field_simp [hφ.ne']
    rw [heγ,hea,heb,hGe,hRsq] at hg
    have hbnd := relative_radius_cauchy_scalar hCb hE (show 0≤2*Hf.toReal by positivity) hI hp hν hR hr hφ hκ
      (show 0≤(1:ℝ) by norm_num)
    dsimp only at hbnd
    simp only [mul_one] at hbnd
    rw [hFe,hRsq] at hbnd
    apply hn.trans
    calc
      _ ≤ ENNReal.ofReal (relativeCauchyConstant Cg E G.toReal*
            min ((I*p^2*ν^2*φ^2/θ^2)*Real.sqrt r)
              ((Real.sqrt I*R*ν*Real.sqrt κ/θ^2)/Real.sqrt r))+
          ENNReal.ofReal (relativeCauchyConstant Cb E (2*Hf.toReal)*
            min ((I*p^2*ν^2*φ)*Real.sqrt r)
              ((Real.sqrt I*R*ν*Real.sqrt κ/φ)/Real.sqrt r)) := by
        exact add_le_add hg hbnd
      _ = _ := by
        rw [←ENNReal.ofReal_add
          (mul_nonneg (relativeCauchyConstant_nonneg hCg) (by positivity))
          (mul_nonneg (relativeCauchyConstant_nonneg hCb) (by positivity))]

  have hshortRadialSum :
      ∃ Cg Cb : ℝ, 0 ≤ Cg ∧ 0 ≤ Cb ∧
      ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
        EnergyPrefix s T → 0 ≤ T → (∀ z,s.f (0,z)=d.f₀ z) →
      ∀ (zX : Phase) (S : Set Phase) (np nθ nφ j : ℕ)
        (a b I len w M A P L massScale Cs : ℝ),
        IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
        0 ≤ a → b ≤ T → a ≤ b → 0 < len → len ≤ I → b-a ≤ I →
        0 < M → 0 ≤ A → 0 < P → 0 ≤ L → 0 < massScale → 0 < w → 128 ≤ Cs →
        massScale ≤ sourceRepresentative np/128 → massScale ≤ w/8 →
        512 ≤ cappedRepresentative j*sourceRepresentative np →
        32 ≤ cappedRepresentative j*w →
        2*len ≤ (Cs*(P/massScale)*(M/cappedRepresentative j+
          Real.sqrt (A*L/cappedRepresentative j)))⁻¹^2 →
        IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P L →
        (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P L) →
        let p := sourceRepresentative np
        let θ := cappedRepresentative nθ
        let φ := cappedRepresentative nφ
        let σ := cappedRepresentative j
        let X := fun t=>(prefixFlow F.flow T zX t).1
        let V := fun t=>(prefixFlow F.flow T zX t).2
        let B := fun nr=>relativeRepresentativeClosedBin T w ![np,nθ,nφ,nr] j
        let E := ∫x : Vec,totalEnergy s (0,x)
        let R := Real.sqrt (1+I/len)
        let ν := min θ σ
        let κ := 1+φ/σ
        let Kg := relativeCauchyConstant Cg E
          (goodFieldBudget s (fun t=>(prefixFlow F.flow T zX t).1) (fun t=>velocity (prefixFlow F.flow T zX t).2) 1 a b I nφ).toReal
        let Kb := relativeCauchyConstant Cb E
          (2*(magneticFieldBudget s F.flow zX T 1 (max 0 (a-2*I)) (min T b) I nφ).toReal)
        let D := dyadicBalanceConstant (1/2) (1/2)
        (∑'nr : ℕ,if max 1 T*cappedRepresentative nr≤I then
          ∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V (B nr) z
            ∂physicalBinMeasure V (B nr) (Icc a b) else 0) ≤
        ENNReal.ofReal (Kg*D*Real.sqrt
          ((I*p^2*ν^2*φ^2/θ^2)*(Real.sqrt I*R*ν*Real.sqrt κ/θ^2))+
          Kb*D*Real.sqrt ((I*p^2*ν^2*φ)*(Real.sqrt I*R*ν*Real.sqrt κ/φ))) := by
    obtain ⟨Cg,Cb,hCg,hCb,hsource⟩ := hshortRadius
    refine ⟨Cg,Cb,hCg,hCb,?_⟩
    intro s T F hs hT h0 zX S np nθ nφ j a b I len w M A P L massScale Cs hS hS0
      ha hb hab hlen hlenI hJI hM hA hP hL hm hw hCs hmq hmw hqσ hwσ hstable HX HZ
    dsimp only
    let p := sourceRepresentative np
    let θ := cappedRepresentative nθ
    let φ := cappedRepresentative nφ
    let σ := cappedRepresentative j
    let ν := min θ σ
    let κ := 1+φ/σ
    let E := ∫x : Vec,totalEnergy s (0,x)
    let R := Real.sqrt (1+I/len)
    let Kg := relativeCauchyConstant Cg E
          (goodFieldBudget s (fun t=>(prefixFlow F.flow T zX t).1) (fun t=>velocity (prefixFlow F.flow T zX t).2) 1 a b I nφ).toReal
    let Kb := relativeCauchyConstant Cb E
          (2*(magneticFieldBudget s F.flow zX T 1 (max 0 (a-2*I)) (min T b) I nφ).toReal)
    let ag := I*p^2*ν^2*φ^2/θ^2
    let bg := Real.sqrt I*R*ν*Real.sqrt κ/θ^2
    let ab := I*p^2*ν^2*φ
    let bb := Real.sqrt I*R*ν*Real.sqrt κ/φ
    let D := dyadicBalanceConstant (1/2) (1/2)
    have hI : 0<I := hlen.trans_le hlenI
    have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
    have hθ : 0<θ := cappedRepresentative_pos _
    have hφ : 0<φ := cappedRepresentative_pos _
    have hσ : 0<σ := cappedRepresentative_pos _
    have hν : 0≤ν := (lt_min hθ hσ).le
    have hag : 0≤ag := by dsimp [ag]; positivity
    have hbg : 0≤bg := by dsimp [bg,R,κ]; positivity
    have hab' : 0≤ab := by dsimp [ab]; positivity
    have hbb : 0≤bb := by dsimp [bb,R,κ]; positivity
    have hKg : 0≤Kg := relativeCauchyConstant_nonneg hCg
    have hKb : 0≤Kb := relativeCauchyConstant_nonneg hCb
    have hD : 0≤D := (dyadicBalanceConstant_pos (by norm_num) (by norm_num)).le
    have hH : 0 < max 1 T := zero_lt_one.trans_le (le_max_left _ _)
    have hpoint (nr : ℕ) := hsource s T F hs hT h0 zX S ![np,nθ,nφ,nr] j
      a b I len w M A P L massScale Cs hS hS0 ha hb hab hlen hlenI hJI
      hM hA hP hL hm hw hCs hmq hmw hqσ hwσ hstable
    calc
      _ ≤ ∑'nr : ℕ, (ENNReal.ofReal (Kg*min (ag*Real.sqrt (max 1 T*cappedRepresentative nr))
          (bg/Real.sqrt (max 1 T*cappedRepresentative nr)))+
        ENNReal.ofReal (Kb*min (ab*Real.sqrt (max 1 T*cappedRepresentative nr))
          (bb/Real.sqrt (max 1 T*cappedRepresentative nr)))) := by
        apply ENNReal.tsum_le_tsum
        intro nr
        split_ifs with hnr
        · have hn := hpoint nr hnr HX HZ
          dsimp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,
            Matrix.cons_val,Fin.reduceFinMk] at hn
          refine hn.trans_eq ?_
          exact ENNReal.ofReal_add (mul_nonneg hKg (by positivity)) (mul_nonneg hKb (by positivity))
        · exact bot_le
      _ ≤ ENNReal.ofReal (Kg*D*Real.sqrt (ag*bg))+
          ENNReal.ofReal (Kb*D*Real.sqrt (ab*bb)) := by
        rw [ENNReal.tsum_add]
        exact add_le_add (capped_sqrt_radius_ennreal_sum hag hbg hH hKg)
          (capped_sqrt_radius_ennreal_sum hab' hbb hH hKb)
      _ = _ := (ENNReal.ofReal_add (by positivity) (by positivity)).symm

  have hbalanceFactor {I p ν R κ φ γ : ℝ}
      (hI : 0<I) (hp : 0≤p) (hν : 0≤ν) (hR : 0≤R) (hκ : 0≤κ)
      (hφ : 0<φ) (hγ : 0≤γ) :
      Real.sqrt ((I*p^2*ν^2*φ*γ)*(Real.sqrt I*R*ν*Real.sqrt κ*γ/φ))=
        (I : ℝ)^(3/4:ℝ)*p*ν^(3/2:ℝ)*Real.sqrt R*κ^(1/4:ℝ)*γ := by
    have he : (I*p^2*ν^2*φ*γ)*(Real.sqrt I*R*ν*Real.sqrt κ*γ/φ)=
        (I*Real.sqrt I)*p^2*ν^3*R*Real.sqrt κ*γ^2 := by field_simp
    have hIs : Real.sqrt (I*Real.sqrt I)=(I : ℝ)^(3/4:ℝ) := by
      rw [Real.sqrt_mul hI.le,Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,←Real.rpow_mul hI.le,
        ←Real.rpow_add hI]
      congr 1
      norm_num
    have hνs : Real.sqrt (ν^3)=ν^(3/2:ℝ) := by
      rw [Real.sqrt_eq_rpow,←Real.rpow_natCast_mul hν]
      norm_num
    have hκs : Real.sqrt (Real.sqrt κ)=κ^(1/4:ℝ) := by
      rw [Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,←Real.rpow_mul hκ]
      congr 1
      norm_num
    rw [he,Real.sqrt_mul (by positivity : 0≤(I*Real.sqrt I)*p^2*ν^3*R*Real.sqrt κ),
      Real.sqrt_mul (by positivity : 0≤(I*Real.sqrt I)*p^2*ν^3*R),
      Real.sqrt_mul (by positivity : 0≤(I*Real.sqrt I)*p^2*ν^3),
      Real.sqrt_mul (by positivity : 0≤(I*Real.sqrt I)*p^2),
      Real.sqrt_mul (by positivity : 0≤I*Real.sqrt I),Real.sqrt_sq hp,Real.sqrt_sq hγ,hIs,hνs,hκs]

  have hgoodBalanceFactor {I p ν R κ φ θ : ℝ}
      (hI : 0<I) (hp : 0≤p) (hν : 0≤ν) (hR : 0≤R) (hκ : 0≤κ)
      (hφ : 0<φ) (hθ : 0<θ) :
      Real.sqrt ((I*p^2*ν^2*φ^2/θ^2)*(Real.sqrt I*R*ν*Real.sqrt κ/θ^2))=
        (I : ℝ)^(3/4:ℝ)*p*ν^(3/2:ℝ)*Real.sqrt R*κ^(1/4:ℝ)*(φ/θ^2) := by
    have he : (I*p^2*ν^2*φ^2/θ^2)*(Real.sqrt I*R*ν*Real.sqrt κ/θ^2)=
        (I*p^2*ν^2*φ*(φ/θ^2))*(Real.sqrt I*R*ν*Real.sqrt κ*(φ/θ^2)/φ) := by
      field_simp
    rw [he]
    exact hbalanceFactor hI hp hν hR hκ hφ (by positivity)

  have hshortFactored :
      ∃ Cg Cb : ℝ, 0 ≤ Cg ∧ 0 ≤ Cb ∧
      ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
        EnergyPrefix s T → 0 ≤ T → (∀ z,s.f (0,z)=d.f₀ z) →
      ∀ (zX : Phase) (S : Set Phase) (np nθ nφ j : ℕ)
        (a b I len w M A P L massScale Cs : ℝ),
        IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
        0 ≤ a → b ≤ T → a ≤ b → 0 < len → len ≤ I → b-a ≤ I →
        0 < M → 0 ≤ A → 0 < P → 0 ≤ L → 0 < massScale → 0 < w → 128 ≤ Cs →
        massScale ≤ sourceRepresentative np/128 → massScale ≤ w/8 →
        512 ≤ cappedRepresentative j*sourceRepresentative np →
        32 ≤ cappedRepresentative j*w →
        2*len ≤ (Cs*(P/massScale)*(M/cappedRepresentative j+
          Real.sqrt (A*L/cappedRepresentative j)))⁻¹^2 →
        IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P L →
        (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P L) →
        let p := sourceRepresentative np
        let θ := cappedRepresentative nθ
        let φ := cappedRepresentative nφ
        let σ := cappedRepresentative j
        let X := fun t=>(prefixFlow F.flow T zX t).1
        let V := fun t=>(prefixFlow F.flow T zX t).2
        let B := fun nr=>relativeRepresentativeClosedBin T w ![np,nθ,nφ,nr] j
        let E := ∫x : Vec,totalEnergy s (0,x)
        let R := Real.sqrt (1+I/len)
        let ν := min θ σ
        let κ := 1+φ/σ
        let Kg := relativeCauchyConstant Cg E
          (goodFieldBudget s (fun t=>(prefixFlow F.flow T zX t).1) (fun t=>velocity (prefixFlow F.flow T zX t).2) 1 a b I nφ).toReal
        let Kb := relativeCauchyConstant Cb E
          (2*(magneticFieldBudget s F.flow zX T 1 (max 0 (a-2*I)) (min T b) I nφ).toReal)
        let D := dyadicBalanceConstant (1/2) (1/2)
        (∑'nr : ℕ,if max 1 T*cappedRepresentative nr≤I then
          ∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V (B nr) z
            ∂physicalBinMeasure V (B nr) (Icc a b) else 0) ≤
        ENNReal.ofReal (D*(I : ℝ)^(3/4:ℝ)*p*Real.sqrt R*
          relativeSourceAngle θ φ σ*(Kg*(φ/θ^2)+Kb)) := by
    obtain ⟨Cg,Cb,hCg,hCb,hsource⟩ := hshortRadialSum
    refine ⟨Cg,Cb,hCg,hCb,?_⟩
    intro s T F hs hT h0 zX S np nθ nφ j a b I len w M A P L massScale Cs hS hS0
      ha hb hab hlen hlenI hJI hM hA hP hL hm hw hCs hmq hmw hqσ hwσ hstable HX HZ
    dsimp only
    have hn := hsource s T F hs hT h0 zX S np nθ nφ j a b I len w M A P L massScale Cs
      hS hS0 ha hb hab hlen hlenI hJI hM hA hP hL hm hw hCs hmq hmw hqσ hwσ hstable HX HZ
    dsimp only at hn
    have hp : 0 ≤ sourceRepresentative np := by dsimp [sourceRepresentative]; positivity
    have hθ := cappedRepresentative_pos nθ
    have hφ := cappedRepresentative_pos nφ
    have hσ := cappedRepresentative_pos j
    have hκ : 0≤1+cappedRepresentative nφ/cappedRepresentative j := by positivity
    have hb := hbalanceFactor (hlen.trans_le hlenI) hp (le_min hθ.le hσ.le)
      (Real.sqrt_nonneg (1+I/len)) hκ hφ (by norm_num : (0:ℝ)≤1)
    simp only [mul_one] at hb
    rw [hgoodBalanceFactor (hlen.trans_le hlenI) hp (le_min hθ.le hσ.le)
      (Real.sqrt_nonneg _) hκ hφ hθ,hb] at hn
    convert hn using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    dsimp [relativeSourceAngle]
    ring

  have hshortClipped :
      ∃ Cg Cb : ℝ, 0 ≤ Cg ∧ 0 ≤ Cb ∧
      ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
        EnergyPrefix s T → 0 ≤ T → (∀ z,s.f (0,z)=d.f₀ z) →
      ∀ (zX : Phase) (S : Set Phase) (np nθ nφ j : ℕ)
        (a b I w M A P : ℝ),
        IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
        0 ≤ a → b ≤ T → a ≤ b → 0 < I → b-a ≤ I →
        0 < M → 0 ≤ A → 0 < P → 0 < w →
        512 ≤ cappedRepresentative j*sourceRepresentative np →
        32 ≤ cappedRepresentative j*w →
        IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
        (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
        let p := sourceRepresentative np
        let θ := cappedRepresentative nθ
        let φ := cappedRepresentative nφ
        let σ := cappedRepresentative j
        let X := fun t=>(prefixFlow F.flow T zX t).1
        let V := fun t=>(prefixFlow F.flow T zX t).2
        let B := fun nr=>relativeRepresentativeClosedBin T w ![np,nθ,nφ,nr] j
        let E := ∫x : Vec,totalEnergy s (0,x)
        let R := Real.sqrt (1+I/min I (stabilityLength P 16384 M A p w σ/2))
        let ν := min θ σ
        let κ := 1+φ/σ
        let Kg := relativeCauchyConstant Cg E
          (goodFieldBudget s (fun t=>(prefixFlow F.flow T zX t).1) (fun t=>velocity (prefixFlow F.flow T zX t).2) 1 a b I nφ).toReal
        let Kb := relativeCauchyConstant Cb E
          (2*(magneticFieldBudget s F.flow zX T 1 (max 0 (a-2*I)) (min T b) I nφ).toReal)
        let D := dyadicBalanceConstant (1/2) (1/2)
        (∑'nr : ℕ,if max 1 T*cappedRepresentative nr≤I then
          ∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V (B nr) z
            ∂physicalBinMeasure V (B nr) (Icc a b) else 0) ≤
        ENNReal.ofReal (D*(I : ℝ)^(3/4:ℝ)*p*Real.sqrt R*
          relativeSourceAngle θ φ σ*(Kg*(φ/θ^2)+Kb)) := by
    obtain ⟨Cg,Cb,hCg,hCb,hsource⟩ := hshortFactored
    refine ⟨Cg,Cb,hCg,hCb,?_⟩
    intro s T F hs hT h0 zX S np nθ nφ j a b I w M A P hS hS0 ha hb hab hI hJI
      hM hA hP hw hpσ hwσ HX HZ
    dsimp only
    let p := sourceRepresentative np
    let σ := cappedRepresentative j
    let L := Real.log (2+P)
    let lam := stabilityLength P 16384 M A p w σ
    let len := min I (lam/2)
    let m := min p w/128
    have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
    have hσ : 0<σ := cappedRepresentative_pos _
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
    exact hsource s T F hs hT h0 zX S np nθ nφ j a b I len w M A P L m 128
      hS hS0 ha hb hab hlen hlenI hJI hM hA hP (Real.log_nonneg (by linarith)) hm hw
      (by norm_num) hmq hmw hpσ hwσ hstable HX HZ
  obtain ⟨Cg,Cb,hCg,hCb,hsource⟩ := hshortClipped
  refine ⟨Cg,Cb,hCg,hCb,?_⟩
  intro s T F hs hT h0 zX S np nφ a b I w M A P hS hS0 ha hb hab hI hJI hM hA hP hw HX HZ
    Sθ Sσ hθ hσ
  dsimp only
  let p := sourceRepresentative np
  let φ := cappedRepresentative nφ
  let E := ∫x : Vec,totalEnergy s (0,x)
  let Kg := relativeCauchyConstant Cg E
    (goodFieldBudget s (fun t=>(prefixFlow F.flow T zX t).1)
      (fun t=>velocity (prefixFlow F.flow T zX t).2) 1 a b I nφ).toReal
  let Kb := relativeCauchyConstant Cb E
    (2*(magneticFieldBudget s F.flow zX T 1 (max 0 (a-2*I)) (min T b) I nφ).toReal)
  let D := dyadicBalanceConstant (1/2) (1/2)
  let R (j : ℕ) := Real.sqrt (Real.sqrt (1+I/min I (stabilityLength P 16384 M A p w (cappedRepresentative j)/2)))
  let U (i j : ℕ) := R j*relativeSourceAngle (cappedRepresentative i) φ (cappedRepresentative j)*
    (Kg*(φ/(cappedRepresentative i)^2)+Kb)
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  have hφ : 0<φ := cappedRepresentative_pos _
  have hKg : 0≤Kg := relativeCauchyConstant_nonneg hCg
  have hKb : 0≤Kb := relativeCauchyConstant_nonneg hCb
  have hD : 0≤D := (dyadicBalanceConstant_pos (by norm_num) (by norm_num)).le
  have hU (i j : ℕ) : 0≤U i j := by
    dsimp only [U]
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (relativeSourceAngle_nonneg
      (cappedRepresentative_pos i).le hφ.le (cappedRepresentative_pos j))) (by positivity)
  have hn := remaining_stable_source_angular hI hP (by norm_num : (0:ℝ)<16384) hM hA hp hw hφ
    (by norm_num : (0:ℝ)<131080) (by norm_num : (0:ℝ)<16384) hKg hKb Sθ Sσ hθ
      (fun i hi j hj=>(hσ i hi j hj).1)
  calc
    _≤∑i∈Sθ,∑j∈Sσ i,ENNReal.ofReal ((D*(I : ℝ)^(3/4:ℝ)*p)*U i j) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      have hh := hsource s T F hs hT h0 zX S np i nφ j a b I w M A P hS hS0 ha hb hab
        hI hJI hM hA hP hw (hσ i hi j hj).2.1 (hσ i hi j hj).2.2 HX HZ
      dsimp only at hh
      simpa only [U,R,D,Kg,Kb,p,φ,E,mul_assoc] using hh
    _=ENNReal.ofReal ((D*(I : ℝ)^(3/4:ℝ)*p)*(∑i∈Sθ,∑j∈Sσ i,U i j)) := by
      rw [Finset.mul_sum]
      rw [ENNReal.ofReal_sum_of_nonneg]
      · apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum,ENNReal.ofReal_sum_of_nonneg]
        exact fun j _=>mul_nonneg (by positivity) (hU i j)
      · intro i hi
        exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun j _=>hU i j))
    _≤_ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hn (by positivity))


end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff



open Set Filter Metric MeasureTheory _root_.Classical
open scoped ENNReal Topology ContDiff



open Set Filter Metric MeasureTheory _root_.Classical
open scoped ENNReal Topology ContDiff


end RVM

end

end OAI
end

theorem solution : type_of% @OAI.RVM.Admissible.direct_source_shared_short_angles_expanded_oai := @OAI.RVM.Admissible.direct_source_shared_short_angles_expanded_oai
