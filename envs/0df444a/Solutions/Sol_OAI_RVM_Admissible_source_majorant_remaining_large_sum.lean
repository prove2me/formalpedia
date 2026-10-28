-- Prove2me | solution 1 for OAI.RVM.Admissible.source_majorant_remaining_large_sum
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:27:44.303287+00:00
-- url     : https://prove2.me/submissions/e67ef792-8f6b-4b66-919e-a19bfc74a2ca

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000
import Theorems.Thm_OAI_RVM_Admissible_source_majorant_large_radius

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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_SourceMajorant
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

lemma majorant_relativeCauchyConstant_nonneg {C E Z : ℝ} (hC : 0≤C) :
    0≤ majorant_relativeCauchyConstant C E Z := by unfold majorant_relativeCauchyConstant; positivity

lemma majorant_capped_sqrt_radius_ennreal_sum {a b H K : ℝ}
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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_MajorantRelativeDensityTimeFar
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

lemma majorant_capped_large_magnetic_ennreal_sum {H p ν θ φ K : ℝ}
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
        have hprod : ν^2*φ≤1 := calc
          _ ≤ 1*φ := mul_le_mul_of_nonneg_right hνsq hφ
          _ ≤ 1 := by simpa only [one_mul] using hφ1
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

lemma majorant_remaining_good_coarse_balance {I p ν θ φ : ℝ}
    (hI : 0<I) (hI1 : I≤1) (hp : 0≤p) (hν : 0≤ν) (hθ : 0<θ)
    (hνθ : ν≤θ) (hθ1 : θ≤1) (hφ : 0≤φ) (hsector : φ≤16384*θ) :
    Real.sqrt ((I*p^2*ν^2*φ^2/θ^2)*(Real.sqrt I*ν/θ^2)) ≤16384*Real.sqrt I*p := by
  have hsqrt : Real.sqrt I≤1 := (Real.sqrt_le_one).mpr hI1
  have hν3 : ν^3≤θ^3 := pow_le_pow_left₀ hν hνθ 3
  have hφ2 : φ^2≤268435456*θ^2 := by nlinarith only [sq_nonneg (16384*θ-φ),hsector,hφ,hθ]
  have hnum : ν^3*φ^2≤268435456*θ^4 := by
    calc
      _ ≤ θ^3*(268435456*θ^2) := mul_le_mul hν3 hφ2 (sq_nonneg _) (by positivity)
      _ = 268435456*θ^4*θ := by ring
      _ ≤ 268435456*θ^4*1 := mul_le_mul_of_nonneg_left hθ1 (by positivity)
      _ = _ := mul_one _
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity,?_⟩
  have hfactor : Real.sqrt I*(ν^3*φ^2)≤268435456*θ^4 := by
    calc
      _ ≤ 1*(268435456*θ^4) := mul_le_mul hsqrt hnum (by positivity) (by norm_num)
      _ = _ := one_mul _
  have he : (I*p^2*ν^2*φ^2/θ^2)*(Real.sqrt I*ν/θ^2)=
      (I*p^2)*(Real.sqrt I*(ν^3*φ^2))/θ^4 := by ring
  rw [he,show (16384*Real.sqrt I*p)^2=268435456*I*p^2 by rw [mul_pow,mul_pow,Real.sq_sqrt hI.le]; ring]
  apply (div_le_iff₀ (pow_pos hθ 4)).mpr
  calc
    _ ≤ (I*p^2)*(268435456*θ^4) := mul_le_mul_of_nonneg_left hfactor (by positivity)
    _ = _ := by ring

lemma Admissible.source_majorant_remaining_large_sum_oai {d : Datum} (hd₀ : Admissible d) :
    ∃ Cg Cb : ℝ, 0 ≤ Cg ∧ 0 ≤ Cb ∧
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀ z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (S : Set Phase) (np nθ nφ j : ℕ) (a b I w : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → b-a ≤ I → 0 < I → I≤1 →
      cappedRepresentative nφ≤16384*cappedRepresentative nθ →
      let p := sourceRepresentative np
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := fun nr=>relativeRepresentativeClosedBin T w ![np,nθ,nφ,nr] j
      let E := ∫x : Vec,totalEnergy s (0,x)
      let Kg := majorant_relativeCauchyConstant Cg E (20*E)
      let Kb := majorant_relativeCauchyConstant Cb E (120*E)
      (∑'nr : ℕ,if I ≤ max 1 T*cappedRepresentative nr then
        ∫⁻z : ConeCoordinate,physicalSourceMajorantDensity s X V (B nr) z
          ∂physicalBinMeasure V (B nr) (Icc a b) else 0) ≤
      ENNReal.ofReal ((16384*Kg*dyadicBalanceConstant (1/2) (1/2)+
        Kb*dyadicBalanceConstant 1 (1/2))*Real.sqrt I*p) := by
  obtain ⟨Cg,Cb,hCg,hCb,hsource⟩ := hd₀.source_majorant_large_radius
  refine ⟨Cg,Cb,hCg,hCb,?_⟩
  intro s T F hs hT h0 zX S np nθ nφ j a b I w hS hS0 ha hb hJI hI hI1 hsector
  dsimp only
  let p := sourceRepresentative np
  let θ := cappedRepresentative nθ
  let φ := cappedRepresentative nφ
  let σ := cappedRepresentative j
  let ν := min θ σ
  let E := ∫x : Vec,totalEnergy s (0,x)
  let Kg := majorant_relativeCauchyConstant Cg E (20*E)
  let Kb := majorant_relativeCauchyConstant Cb E (120*E)
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
  have hKg : 0≤Kg := majorant_relativeCauchyConstant_nonneg hCg
  have hKb : 0≤Kb := majorant_relativeCauchyConstant_nonneg hCb
  have hH : 0 < max 1 T := zero_lt_one.trans_le (le_max_left _ _)
  have hg := majorant_capped_sqrt_radius_ennreal_sum (show 0≤ag by dsimp [ag]; positivity)
    (show 0≤bg by dsimp [bg]; positivity) hH hKg
  have hm := majorant_capped_large_magnetic_ennreal_sum hH hp hν.le hθ (min_le_left _ _)
    ((min_le_left _ _).trans (cappedRepresentative_le_one _)) hφ.le
    (cappedRepresentative_le_one _) (mul_nonneg hKb (Real.sqrt_nonneg I))
  have hc := majorant_remaining_good_coarse_balance hI hI1 hp.le hν.le hθ (min_le_left _ _)
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
        _ ≤ Kg*dyadicBalanceConstant (1/2) (1/2)*(16384*Real.sqrt I*p)+
            Kb*Real.sqrt I*dyadicBalanceConstant 1 (1/2)*p :=
          add_le_add (mul_le_mul_of_nonneg_left hc (mul_nonneg hKg hDs)) le_rfl
        _ = _ := by dsimp only [Kg,Kb,p,E]; ring

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

end

end OAI
end

theorem solution : type_of% @OAI.RVM.Admissible.source_majorant_remaining_large_sum_oai := @OAI.RVM.Admissible.source_majorant_remaining_large_sum_oai
