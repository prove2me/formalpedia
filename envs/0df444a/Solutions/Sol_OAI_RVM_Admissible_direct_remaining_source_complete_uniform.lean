-- Prove2me | solution 1 for OAI.RVM.Admissible.direct_remaining_source_complete_uniform
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:37:46.262648+00:00
-- url     : https://prove2.me/submissions/9c7e35b4-18df-4a6c-bdc2-73e9300aba77

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000
import Theorems.Thm_OAI_RVM_Admissible_direct_remaining_source_deficit_short_uniform_expanded
import Theorems.Thm_OAI_RVM_Admissible_direct_remaining_source_short_uniform_expanded
import Theorems.Thm_OAI_RVM_Admissible_direct_source_large_radius

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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_MomentumDirection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RVM

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
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff NNReal ENNReal
open Set
open scoped Topology ContDiff RealInnerProductSpace
open Set MeasureTheory
open scoped ENNReal
open scoped Topology ContDiff ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff



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


lemma sourceRepresentative_sum_bound {x : ℝ} (hx : 0≤x) (S : Finset ℕ)
    (hS : ∀n∈S,sourceRepresentative n≤x) : ∑n∈S,sourceRepresentative n≤2*x := by
  classical
  have hgeom (N : ℕ) : ∑n∈Finset.range (N+1),sourceRepresentative n≤2*sourceRepresentative N := by
    induction N with
    | zero => norm_num [sourceRepresentative]
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have he : sourceRepresentative (N+1)=2*sourceRepresentative N := by
        dsimp only [sourceRepresentative]
        rw [pow_succ]
        ring
      rw [he]
      linarith
  by_cases hne : S.Nonempty
  · let N := S.max' hne
    have hsub : S⊆Finset.range (N+1) := by
      intro n hn
      apply Finset.mem_range.mpr
      have hh := S.le_max' n hn
      change n≤N at hh
      omega
    have hs : (∑n∈S,sourceRepresentative n)≤∑n∈Finset.range (N+1),sourceRepresentative n :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _=>by dsimp only [sourceRepresentative]; positivity)
    exact hs.trans ((hgeom N).trans (mul_le_mul_of_nonneg_left (hS N (S.max'_mem hne)) (by norm_num)))
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.sum_empty]
    positivity

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

lemma capped_positive_power_sum {x α : ℝ} (hx : 0<x) (hα : 0<α)
    (S : Finset ℕ) (hS : ∀j∈S,cappedRepresentative j≤x) :
    ∑j∈S,(cappedRepresentative j/x)^α≤(1-((2:ℝ)⁻¹)^α)⁻¹ := by
  classical
  have hbase : 0<((2:ℝ)⁻¹)^α := Real.rpow_pos_of_pos (by norm_num) _
  have hbase1 : ((2:ℝ)⁻¹)^α<1 := Real.rpow_lt_one (by norm_num) (by norm_num) hα
  have hnorm : ‖((2:ℝ)⁻¹)^α‖<1 := by rw [Real.norm_eq_abs,abs_of_pos hbase]; exact hbase1
  by_cases hne : S.Nonempty
  · let j₀ := S.min' hne
    have hj₀ : j₀∈S := S.min'_mem hne
    have hjmin (j : ℕ) (hj : j∈S) : j₀≤j := S.min'_le j hj
    have hp (j : ℕ) (hj : j∈S) : cappedRepresentative j/x≤((2:ℝ)⁻¹)^(j-j₀) := by
      have he : cappedRepresentative j=cappedRepresentative j₀*((2:ℝ)⁻¹)^(j-j₀) := by
        dsimp only [cappedRepresentative]
        rw [←pow_add,Nat.add_sub_of_le (hjmin j hj)]
      rw [he]
      apply (div_le_iff₀ hx).mpr
      have hh := mul_le_mul_of_nonneg_right (hS j₀ hj₀)
        (pow_nonneg (by norm_num : (0:ℝ)≤2⁻¹) (j-j₀))
      simpa only [mul_comm] using hh
    have hpoint (j : ℕ) (hj : j∈S) : (cappedRepresentative j/x)^α≤(((2:ℝ)⁻¹)^α)^(j-j₀) := by
      rw [Real.rpow_pow_comm (by norm_num : (0:ℝ)≤2⁻¹)]
      exact Real.rpow_le_rpow (div_nonneg (cappedRepresentative_pos j).le hx.le) (hp j hj) hα.le
    have hinj : Set.InjOn (fun j : ℕ=>j-j₀) S := by
      intro i hi j hj hij
      have hi' := hjmin i hi
      have hj' := hjmin j hj
      change i-j₀=j-j₀ at hij
      omega
    calc
      _ ≤ ∑j∈S,(((2:ℝ)⁻¹)^α)^(j-j₀) := Finset.sum_le_sum hpoint
      _ = ∑m∈S.image (fun j=>j-j₀),(((2:ℝ)⁻¹)^α)^m := (Finset.sum_image hinj).symm
      _ ≤ ∑'m : ℕ,(((2:ℝ)⁻¹)^α)^m :=
        (summable_geometric_of_norm_lt_one hnorm).sum_le_tsum _ (fun _ _=>by positivity)
      _ = _ := tsum_geometric_of_norm_lt_one hnorm
  · have he : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [he,Finset.sum_empty]
    exact inv_nonneg.mpr (sub_nonneg.mpr hbase1.le)

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


lemma capped_positive_power_sum_unscaled {x α : ℝ} (hx : 0<x) (hα : 0<α)
    (S : Finset ℕ) (hS : ∀j∈S,cappedRepresentative j≤x) :
    ∑j∈S,(cappedRepresentative j)^α≤(1-((2:ℝ)⁻¹)^α)⁻¹*x^α := by
  have hh := capped_positive_power_sum hx hα S hS
  have he (j : ℕ) : (cappedRepresentative j/x)^α=(cappedRepresentative j)^α/x^α :=
    Real.div_rpow (cappedRepresentative_pos j).le hx.le α
  simp_rw [he] at hh
  rw [←Finset.sum_div] at hh
  exact (div_le_iff₀ (Real.rpow_pos_of_pos hx α)).mp hh

lemma large_radius_magnetic_relative_sum {p θ φ K : ℝ}
    (hp : 0≤p) (hθ : 0<θ) (hφ : 0≤φ) (hK : 0<K)
    (S : Finset ℕ) (hS : ∀j∈S,cappedRepresentative j≤K*θ) :
    ∑j∈S,p*(min θ (cappedRepresentative j))^(4/3:ℝ)*θ^(-(2/3:ℝ))*φ^(1/3:ℝ)≤
      (1-((2:ℝ)⁻¹)^(4/3:ℝ))⁻¹*K^(4/3:ℝ)*p*θ^(2/3:ℝ)*φ^(1/3:ℝ) := by
  have hsum := capped_positive_power_sum_unscaled (mul_pos hK hθ) (by norm_num : (0:ℝ)<4/3) S hS
  have he : (K*θ)^(4/3:ℝ)*θ^(-(2/3:ℝ))=K^(4/3:ℝ)*θ^(2/3:ℝ) := by
    rw [Real.mul_rpow hK.le hθ.le,mul_assoc,←Real.rpow_add hθ]
    congr 2
    norm_num
  calc
    _ ≤ ∑j∈S,p*(cappedRepresentative j)^(4/3:ℝ)*θ^(-(2/3:ℝ))*φ^(1/3:ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      have hm := Real.rpow_le_rpow (le_min hθ.le (cappedRepresentative_pos j).le)
        (min_le_right θ (cappedRepresentative j)) (by norm_num : (0:ℝ)≤4/3)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm hp)
          (Real.rpow_nonneg hθ.le _)) (Real.rpow_nonneg hφ _)
    _ = p*(∑j∈S,(cappedRepresentative j)^(4/3:ℝ))*θ^(-(2/3:ℝ))*φ^(1/3:ℝ) := by
      simp only [Finset.sum_mul,Finset.mul_sum]
    _ ≤ p*((1-((2:ℝ)⁻¹)^(4/3:ℝ))⁻¹*(K*θ)^(4/3:ℝ))*θ^(-(2/3:ℝ))*φ^(1/3:ℝ) := by
      gcongr
    _ = _ := by
      calc
        _ = (1-((2:ℝ)⁻¹)^(4/3:ℝ))⁻¹*p*((K*θ)^(4/3:ℝ)*θ^(-(2/3:ℝ)))*φ^(1/3:ℝ) := by ring
        _ = _ := by rw [he]; ring


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

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_DirectionCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RVM

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff


open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff



open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff


lemma SmoothClassicalPrefix.initial_energy_eq {d : Datum} {s : Solution} {T : ℝ}
    (hs : SmoothClassicalPrefix d s T) :
    (∫x : Vec,totalEnergy s (0,x))=datumEnergyNumber d := by
  unfold totalEnergy particleEnergy datumEnergyNumber
  simp only [hs.initial_E,hs.initial_B,hs.initial_f]

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_DirectionOverlap
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
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

lemma SmoothClassicalPrefix.energyPrefix {d : Datum} {s : Solution} {H : ℝ}
    (hs : SmoothClassicalPrefix d s H) : EnergyPrefix s H := by
  refine ⟨(hs.f_smooth.of_le (by decide)).mono (fun _ hp => hp.1),
    (hs.E_smooth.of_le (by decide)).mono (fun _ hp => hp.1),
    (hs.B_smooth.of_le (by decide)).mono (fun _ hp => hp.1),hs.nonnegative,
    hs.E_L2,hs.B_L2,hs.compact,?_,?_⟩
  · intro t ht x v
    have hh := (hs.equations t ht.1.le ht.2).1 x v
    rwa [derivWithin_of_mem_nhds (Ici_mem_nhds ht.1)] at hh
  · intro t ht x
    have he := (hs.equations t ht.1.le ht.2).2.1 x
    have hb := (hs.equations t ht.1.le ht.2).2.2.1 x
    rw [derivWithin_of_mem_nhds (Ici_mem_nhds ht.1)] at he hb
    exact ⟨he,hb⟩

end RVM

open Set MeasureTheory
open scoped ENNReal

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
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

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


lemma capped_inverse_power_sum {x α : ℝ} (hx : 0<x) (hα : 0<α)
    (S : Finset ℕ) (hS : ∀j∈S,x ≤ cappedRepresentative j) :
    ∑j∈S,(x/cappedRepresentative j)^α≤(1-((2:ℝ)⁻¹)^α)⁻¹ := by
  have hbase : 0<((2:ℝ)⁻¹)^α := Real.rpow_pos_of_pos (by norm_num) _
  have hbase1 : ((2:ℝ)⁻¹)^α<1 := Real.rpow_lt_one (by norm_num) (by norm_num) hα
  have hnorm : ‖((2:ℝ)⁻¹)^α‖<1 := by rw [Real.norm_eq_abs,abs_of_pos hbase]; exact hbase1
  by_cases hne : S.Nonempty
  · let j₀ := S.max' hne
    have hj₀ : j₀∈S := S.max'_mem hne
    have hjmax (j : ℕ) (hj : j∈S) : j≤j₀ := S.le_max' j hj
    have hp (j : ℕ) (hj : j∈S) : x/cappedRepresentative j≤((2:ℝ)⁻¹)^(j₀-j) := by
      have he : cappedRepresentative j₀=cappedRepresentative j*((2:ℝ)⁻¹)^(j₀-j) := by
        dsimp only [cappedRepresentative]
        rw [←pow_add,Nat.add_sub_of_le (hjmax j hj)]
      apply (div_le_iff₀ (cappedRepresentative_pos j)).mpr
      rw [mul_comm,←he]
      exact hS j₀ hj₀
    have hpoint (j : ℕ) (hj : j∈S) : (x/cappedRepresentative j)^α≤(((2:ℝ)⁻¹)^α)^(j₀-j) := by
      rw [Real.rpow_pow_comm (by norm_num : (0:ℝ)≤2⁻¹)]
      exact Real.rpow_le_rpow (div_nonneg hx.le (cappedRepresentative_pos j).le) (hp j hj) hα.le
    have hinj : Set.InjOn (fun j : ℕ=>j₀-j) S := by
      intro i hi j hj hij
      have hi' := hjmax i hi
      have hj' := hjmax j hj
      change j₀-i=j₀-j at hij
      omega
    calc
      _ ≤ ∑j∈S,(((2:ℝ)⁻¹)^α)^(j₀-j) := Finset.sum_le_sum hpoint
      _ = ∑m∈S.image (fun j=>j₀-j),(((2:ℝ)⁻¹)^α)^m := (Finset.sum_image hinj).symm
      _ ≤ ∑'m : ℕ,(((2:ℝ)⁻¹)^α)^m :=
        (summable_geometric_of_norm_lt_one hnorm).sum_le_tsum _ (fun _ _=>by positivity)
      _ = _ := tsum_geometric_of_norm_lt_one hnorm
  · have he : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [he,Finset.sum_empty]
    exact inv_nonneg.mpr (sub_nonneg.mpr hbase1.le)

lemma relative_occupation_angular_sum {θ φ K κ e : ℝ} (hθ : 0<θ) (hφ : 0≤φ)
    (hK : 0<K) (hκ : 0≤κ) (he : 1/4<e) (hsector : φ≤κ*θ)
    (S : Finset ℕ) (hS : ∀j∈S,cappedRepresentative j≤K*θ) :
    ∑j∈S,(cappedRepresentative j)^e*(1+φ/cappedRepresentative j)^(1/4:ℝ) ≤
    (((1-((2:ℝ)⁻¹)^e)⁻¹)*K^e+
      ((1-((2:ℝ)⁻¹)^(e-1/4))⁻¹)*K^(e-1/4)*κ^(1/4:ℝ))*θ^e := by
  have he0 : 0<e := by linarith
  have hsub : 0<e-1/4 := by linarith
  have hsum := capped_positive_power_sum_unscaled (mul_pos hK hθ) he0 S hS
  have hsum' := capped_positive_power_sum_unscaled (mul_pos hK hθ) hsub S hS
  have hpoint (j : ℕ) : (cappedRepresentative j)^e*(1+φ/cappedRepresentative j)^(1/4:ℝ) ≤
      (cappedRepresentative j)^e+φ^(1/4:ℝ)*(cappedRepresentative j)^(e-1/4) := by
    have hσ := cappedRepresentative_pos j
    have hq := Real.rpow_add_le_add_rpow (by norm_num : (0:ℝ)≤1)
      (div_nonneg hφ hσ.le) (by norm_num : (0:ℝ)≤1/4) (by norm_num : (1/4:ℝ)≤1)
    rw [Real.one_rpow,Real.div_rpow hφ hσ.le] at hq
    calc
      _≤(cappedRepresentative j)^e*(1+φ^(1/4:ℝ)/(cappedRepresentative j)^(1/4:ℝ)) :=
        mul_le_mul_of_nonneg_left hq (Real.rpow_nonneg hσ.le _)
      _= _ := by rw [Real.rpow_sub hσ]; ring
  have hφpow := Real.rpow_le_rpow hφ hsector (by norm_num : (0:ℝ)≤1/4)
  have heq : θ^(e-1/4)*θ^(1/4:ℝ)=θ^e := by rw [←Real.rpow_add hθ]; congr 1; ring
  calc
    _ ≤ ∑j∈S,((cappedRepresentative j)^e+φ^(1/4:ℝ)*(cappedRepresentative j)^(e-1/4)) :=
      Finset.sum_le_sum (fun j _=>hpoint j)
    _ = (∑j∈S,(cappedRepresentative j)^e)+φ^(1/4:ℝ)*(∑j∈S,(cappedRepresentative j)^(e-1/4)) := by
      rw [Finset.sum_add_distrib,Finset.mul_sum]
    _ ≤ ((1-((2:ℝ)⁻¹)^e)⁻¹)*(K*θ)^e+
        (κ*θ)^(1/4:ℝ)*(((1-((2:ℝ)⁻¹)^(e-1/4))⁻¹)*(K*θ)^(e-1/4)) := by
      apply add_le_add hsum
      apply mul_le_mul hφpow hsum' (Finset.sum_nonneg (fun j _=>Real.rpow_nonneg (cappedRepresentative_pos j).le _))
      exact Real.rpow_nonneg (mul_nonneg hκ hθ.le) _
    _ = _ := by
      rw [Real.mul_rpow hK.le hθ.le,Real.mul_rpow hκ hθ.le,Real.mul_rpow hK.le hθ.le]
      calc
        _ = (((1-((2:ℝ)⁻¹)^e)⁻¹)*K^e)*θ^e+
          (((1-((2:ℝ)⁻¹)^(e-1/4))⁻¹)*K^(e-1/4)*κ^(1/4:ℝ))*(θ^(e-1/4)*θ^(1/4:ℝ)) := by ring
        _ = _ := by rw [heq]; ring

lemma relativeAngularConstant_nonneg {K κ e : ℝ} (hK : 0≤K) (hκ : 0≤κ) (he : 1/4<e) :
    0 ≤ relativeAngularConstant K κ e := by
  have h0 : 0≤e := by linarith
  have h1 : 0≤e-1/4 := by linarith
  unfold relativeAngularConstant
  apply add_nonneg
  · exact mul_nonneg (inv_nonneg.mpr (sub_nonneg.mpr (Real.rpow_le_one (by norm_num) (by norm_num) h0))) (Real.rpow_nonneg hK _)
  · exact mul_nonneg (mul_nonneg (inv_nonneg.mpr (sub_nonneg.mpr (Real.rpow_le_one (by norm_num) (by norm_num) h1))) (Real.rpow_nonneg hK _)) (Real.rpow_nonneg hκ _)

lemma relative_source_angle_sum {θ φ K κ β : ℝ} (hθ : 0<θ) (hφ : 0≤φ)
    (hK : 0<K) (hκ : 0≤κ) (_hβ : 0≤β) (hβ1 : β≤1/2) (hsector : φ≤κ*θ)
    (S : Finset ℕ) (hS : ∀j∈S,cappedRepresentative j≤K*θ) :
    ∑j∈S,relativeSourceAngle θ φ (cappedRepresentative j)/(cappedRepresentative j)^β ≤
      relativeAngularConstant K κ (3/2-β)*θ^(3/2-β) := by
  have he : 1/4<3/2-β := by linarith
  apply le_trans _ (relative_occupation_angular_sum hθ hφ hK hκ he hsector S hS)
  apply Finset.sum_le_sum
  intro j hj
  have hσ := cappedRepresentative_pos j
  have hq : 0≤1+φ/cappedRepresentative j := by positivity
  calc
    _ ≤ ((cappedRepresentative j)^(3/2:ℝ)*(1+φ/cappedRepresentative j)^(1/4:ℝ))/(cappedRepresentative j)^β := by
      apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg hσ.le _)
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hq _)
      exact Real.rpow_le_rpow (le_min hθ.le hσ.le) (min_le_right _ _) (by norm_num)
    _ = _ := by rw [Real.rpow_sub hσ]; ring

lemma capped_lower_weighted_power_sum {φ κ α : ℝ} (hφ : 0<φ) (hκ : 0<κ) (hα : 0<α)
    (S : Finset ℕ) (hS : ∀i∈S,φ≤κ*cappedRepresentative i) :
    ∑i∈S,φ*(cappedRepresentative i)^(-α) ≤
    (1-((2:ℝ)⁻¹)^α)⁻¹*κ^α*φ^(1-α) := by
  have hsum := capped_inverse_power_sum (div_pos hφ hκ) hα S
    (fun i hi=>(div_le_iff₀ hκ).mpr (by nlinarith only [hS i hi]))
  have he (i : ℕ) : φ*(cappedRepresentative i)^(-α)=
      (κ^α*φ^(1-α))*((φ/κ)/cappedRepresentative i)^α := by
    have hσ := cappedRepresentative_pos i
    rw [Real.rpow_neg hσ.le,Real.rpow_sub hφ,Real.rpow_one,
      Real.div_rpow (div_nonneg hφ.le hκ.le) hσ.le,Real.div_rpow hφ.le hκ.le]
    field_simp [(Real.rpow_pos_of_pos hκ α).ne',(Real.rpow_pos_of_pos hφ α).ne',
      (Real.rpow_pos_of_pos hσ α).ne']
  calc
    _ = (κ^α*φ^(1-α))*(∑i∈S,((φ/κ)/cappedRepresentative i)^α) := by simp_rw [he]; rw [Finset.mul_sum]
    _ ≤ (κ^α*φ^(1-α))*(1-((2:ℝ)⁻¹)^α)⁻¹ :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

lemma remaining_good_fixed_receiver_sum {φ K κ β : ℝ} (hφ : 0<φ)
    (hK : 0<K) (hκ : 0<κ) (hβ : 0≤β) (hβ1 : β≤1/2)
    (Sθ : Finset ℕ) (Sσ : ℕ→Finset ℕ)
    (hθ : ∀i∈Sθ,φ≤κ*cappedRepresentative i)
    (hσ : ∀i∈Sθ,∀j∈Sσ i,cappedRepresentative j≤K*cappedRepresentative i) :
    ∑i∈Sθ,∑j∈Sσ i,
      (φ/(cappedRepresentative i)^2)*
        (relativeSourceAngle (cappedRepresentative i) φ (cappedRepresentative j)/(cappedRepresentative j)^β) ≤
    relativeAngularConstant K κ (3/2-β)*(1-((2:ℝ)⁻¹)^(1/2+β))⁻¹*
      κ^(1/2+β)*φ^(1/2-β) := by
  let C := relativeAngularConstant K κ (3/2-β)
  have hC : 0≤C := relativeAngularConstant_nonneg hK.le hκ.le (by linarith)
  have hp (i : ℕ) (hi : i∈Sθ) := relative_source_angle_sum (cappedRepresentative_pos i)
    hφ.le hK hκ.le hβ hβ1 (hθ i hi) (Sσ i) (hσ i hi)
  have he (i : ℕ) : (φ/(cappedRepresentative i)^2)*(C*(cappedRepresentative i)^(3/2-β))=
      C*(φ*(cappedRepresentative i)^(-(1/2+β))) := by
    have hc := cappedRepresentative_pos i
    rw [show -(1/2+β)=3/2-β-2 by ring]
    simp only [Real.rpow_sub hc,Real.rpow_two]
    ring
  have hs := capped_lower_weighted_power_sum hφ hκ (show 0<(1/2:ℝ)+β by linarith) Sθ hθ
  calc
    _ ≤ ∑i∈Sθ,(φ/(cappedRepresentative i)^2)*(C*(cappedRepresentative i)^(3/2-β)) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [←Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hp i hi) (by positivity)
    _ = C*(∑i∈Sθ,φ*(cappedRepresentative i)^(-(1/2+β))) := by simp_rw [he]; rw [Finset.mul_sum]
    _ ≤ C*((1-((2:ℝ)⁻¹)^(1/2+β))⁻¹*κ^(1/2+β)*φ^(1-(1/2+β))) :=
      mul_le_mul_of_nonneg_left hs hC
    _ = _ := by rw [show (1:ℝ)-(1/2+β)=1/2-β by ring]; dsimp [C]; ring


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

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_SharedBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

namespace RVM

lemma relative_source_balance_factor {I p ν R κ φ γ : ℝ}
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

lemma relative_source_good_balance_factor {I p ν R κ φ θ : ℝ}
    (hI : 0<I) (hp : 0≤p) (hν : 0≤ν) (hR : 0≤R) (hκ : 0≤κ)
    (hφ : 0<φ) (hθ : 0<θ) :
    Real.sqrt ((I*p^2*ν^2*φ^2/θ^2)*(Real.sqrt I*R*ν*Real.sqrt κ/θ^2))=
      (I : ℝ)^(3/4:ℝ)*p*ν^(3/2:ℝ)*Real.sqrt R*κ^(1/4:ℝ)*(φ/θ^2) := by
  have he : (I*p^2*ν^2*φ^2/θ^2)*(Real.sqrt I*R*ν*Real.sqrt κ/θ^2)=
      (I*p^2*ν^2*φ*(φ/θ^2))*(Real.sqrt I*R*ν*Real.sqrt κ*(φ/θ^2)/φ) := by
    field_simp
  rw [he]
  exact relative_source_balance_factor hI hp hν hR hκ hφ (by positivity)

lemma rpow_three_quarters_le_sqrt {I : ℝ} (hI : 0<I) (hI1 : I≤1) :
    (I : ℝ)^(3/4:ℝ)≤Real.sqrt I := by
  rw [Real.sqrt_eq_rpow]
  exact Real.rpow_le_rpow_of_exponent_ge hI hI1 (by norm_num)

lemma remainingGoodConstant_nonneg {K κ β : ℝ} (hK : 0≤K) (hκ : 0≤κ)
    (hβ : 0≤β) (hβ1 : β≤1/2) : 0 ≤ remainingGoodConstant K κ β := by
  unfold remainingGoodConstant
  exact mul_nonneg (mul_nonneg (relativeAngularConstant_nonneg hK hκ (by linarith))
    (inv_nonneg.mpr (sub_nonneg.mpr (Real.rpow_le_one (by norm_num) (by norm_num) (by linarith)))))
    (Real.rpow_nonneg hκ _)

end RVM

end

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_DirectLargeAngularSharp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

namespace RVM

lemma directDyadicPowerConstant_nonneg {α : ℝ} (hα : 0≤α) : 0≤directDyadicPowerConstant α := by
  exact inv_nonneg.mpr (sub_nonneg.mpr (Real.rpow_le_one (by norm_num) (by norm_num) hα))

end RVM

end

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

namespace RVM

lemma capped_large_magnetic_sharp_ennreal_sum {H p θ φ σ K : ℝ}
    (hH : 0<H) (hp : 0<p) (hθ : 0<θ) (hφ : 0<φ) (hσ : 0<σ) (hK : 0≤K) :
    (∑'n : ℕ,ENNReal.ofReal (K*min
      (H*cappedRepresentative n*p^2*(min θ σ)^2*φ)
      (Real.sqrt p*(min θ σ)/(θ*Real.sqrt (H*cappedRepresentative n)))))≤
      ENNReal.ofReal (K*dyadicBalanceConstant 1 (1/2)*
        (p*(min θ σ)^(4/3:ℝ)*θ^(-(2/3:ℝ))*φ^(1/3:ℝ))) := by
  let g : ℤ→ℝ := fun k=>min (H*(2:ℝ)^k*p^2*(min θ σ)^2*φ)
    (Real.sqrt p*(min θ σ)/(θ*Real.sqrt (H*(2:ℝ)^k)))
  have hν : 0 < min θ σ := lt_min hθ hσ
  have hg0 (k : ℤ) : 0≤g k := by dsimp [g]; positivity
  have hg := large_radius_magnetic_balance hH hp hθ hφ hσ
  have he (n : ℕ) : cappedRepresentative n=(2:ℝ)^(-(n:ℤ)) := by
    simp only [cappedRepresentative,zpow_neg,zpow_natCast,inv_pow]
  have hinj : Function.Injective (fun n : ℕ=>-(n:ℤ)) := by
    intro a b hab
    exact_mod_cast neg_injective hab
  calc
    _=∑'n : ℕ,ENNReal.ofReal (K*g (-(n:ℤ))) := by simp_rw [he]; rfl
    _≤∑'k : ℤ,ENNReal.ofReal (K*g k) :=
      ENNReal.tsum_comp_le_tsum_of_injective hinj (fun k=>ENNReal.ofReal (K*g k))
    _=ENNReal.ofReal (K*∑'k : ℤ,g k) := by
      rw [←ENNReal.ofReal_tsum_of_nonneg (fun k=>mul_nonneg hK (hg0 k)) (hg.1.mul_left K),tsum_mul_left]
    _≤_ := by
      apply ENNReal.ofReal_le_ofReal
      simpa only [g,mul_assoc] using mul_le_mul_of_nonneg_left hg.2 hK

lemma direct_large_good_balance {I p θ φ σ : ℝ}
    (hI : 0<I) (hp : 0≤p) (hθ : 0<θ) (hφ : 0<φ) (hσ : 0≤σ) :
    Real.sqrt ((I*p^2*(min θ σ)^2*φ^2/θ^2)*(Real.sqrt I*(min θ σ)/θ^2))=
      (I : ℝ)^(3/4:ℝ)*p*(min θ σ)^(3/2:ℝ)*(φ/θ^2) := by
  simpa only [Real.sqrt_one,Real.one_rpow,mul_one] using
    relative_source_good_balance_factor hI hp (le_min hθ.le hσ)
      (by norm_num : (0:ℝ)≤1) (by norm_num : (0:ℝ)≤1) hφ hθ

lemma Admissible.direct_source_large_sharp_sum {d : Datum} (hd : Admissible d) :
    ∃Cg Cb : ℝ,0≤Cg ∧ 0≤Cb ∧
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0≤T → (∀z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (S : Set Phase) (np nt nf j : ℕ) (a b I w : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0≤a → b≤T → b-a≤I → 0<I →
      let p := sourceRepresentative np
      let θ := cappedRepresentative nt
      let φ := cappedRepresentative nf
      let σ := cappedRepresentative j
      let ν := min θ σ
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := fun nr=>relativeRepresentativeClosedBin T w ![np,nt,nf,nr] j
      let E := ∫x : Vec,totalEnergy s (0,x)
      let Kg := relativeCauchyConstant Cg E (20*E)
      let Kb := relativeCauchyConstant Cb E (120*E)
      (∑'nr : ℕ,if I ≤ max 1 T*cappedRepresentative nr then
        ∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V (B nr) z
          ∂physicalBinMeasure V (B nr) (Icc a b) else 0)≤
      ENNReal.ofReal (Kg*dyadicBalanceConstant (1/2) (1/2)*
        ((I : ℝ)^(3/4:ℝ)*p*ν^(3/2:ℝ)*(φ/θ^2))+
        Kb*Real.sqrt I*dyadicBalanceConstant 1 (1/2)*
          (p*ν^(4/3:ℝ)*θ^(-(2/3:ℝ))*φ^(1/3:ℝ))) := by
  obtain ⟨Cg,Cb,hCg,hCb,hsource⟩ := hd.direct_source_large_radius
  refine ⟨Cg,Cb,hCg,hCb,?_⟩
  intro s T F hs hT h0 zX S np nt nf j a b I w hS hS0 ha hb hJI hI
  dsimp only
  let p := sourceRepresentative np
  let θ := cappedRepresentative nt
  let φ := cappedRepresentative nf
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
  have hσ : 0<σ := cappedRepresentative_pos _
  have hν : 0<ν := lt_min hθ hσ
  have hKg : 0≤Kg := relativeCauchyConstant_nonneg hCg
  have hKb : 0≤Kb := relativeCauchyConstant_nonneg hCb
  have hH : 0 < max 1 T := zero_lt_one.trans_le (le_max_left _ _)
  have hg := capped_sqrt_radius_ennreal_sum (show 0≤ag by dsimp [ag]; positivity)
    (show 0≤bg by dsimp [bg]; positivity) hH hKg
  have hm := capped_large_magnetic_sharp_ennreal_sum hH hp hθ hφ hσ
    (mul_nonneg hKb (Real.sqrt_nonneg I))
  have he : Real.sqrt (ag*bg)=(I : ℝ)^(3/4:ℝ)*p*ν^(3/2:ℝ)*(φ/θ^2) :=
    direct_large_good_balance hI hp.le hθ hφ hσ.le
  rw [he] at hg
  have hDs : 0≤dyadicBalanceConstant (1/2) (1/2) :=
    (dyadicBalanceConstant_pos (by norm_num) (by norm_num)).le
  have hDm : 0≤dyadicBalanceConstant 1 (1/2) :=
    (dyadicBalanceConstant_pos (by norm_num) (by norm_num)).le
  calc
    _≤∑'n : ℕ,(G n+Bm n) := by
      apply ENNReal.tsum_le_tsum
      intro n
      split_ifs with hIr
      · have h := hsource s T F hs hT h0 zX S ![np,nt,nf,n] j a b I w hS hS0 ha hb hJI hI hIr
        dsimp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,Matrix.cons_val,Fin.reduceFinMk] at h
        have hrad : 0 < max 1 T*cappedRepresentative n := mul_pos hH (cappedRepresentative_pos _)
        refine h.trans_eq ?_
        exact ENNReal.ofReal_add
          (mul_nonneg hKg (by positivity))
          (mul_nonneg (mul_nonneg hKb (Real.sqrt_nonneg I)) (le_min (by positivity) (by positivity)))
      · exact bot_le
    _=(∑'n : ℕ,G n)+(∑'n : ℕ,Bm n) := ENNReal.tsum_add
    _≤_ := by
      have hh := add_le_add hg hm
      rw [←ENNReal.ofReal_add (by positivity) (by positivity)] at hh
      exact hh

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_DirectExpandedLargeAngular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

namespace RVM

lemma remaining_large_good_receiver_expanded {φ : ℝ} (hφ : 0<φ)
    (Sθ : Finset ℕ) (Sσ : ℕ→Finset ℕ)
    (hθ : ∀i∈Sθ,φ≤16384*cappedRepresentative i)
    (hσ : ∀i∈Sθ,∀j∈Sσ i,cappedRepresentative j≤131080*cappedRepresentative i) :
    (∑i∈Sθ,∑j∈Sσ i,(min (cappedRepresentative i) (cappedRepresentative j))^(3/2:ℝ)*
      (φ/(cappedRepresentative i)^2)) ≤ remainingGoodConstant 131080 16384 0*Real.sqrt φ := by
  have hh := remaining_good_fixed_receiver_sum hφ (by norm_num : (0:ℝ)<131080)
    (by norm_num : (0:ℝ)<16384) (by norm_num : (0:ℝ)≤0) (by norm_num) Sθ Sσ hθ hσ
  simp only [Real.rpow_zero,div_one,add_zero,sub_zero,←Real.sqrt_eq_rpow] at hh
  simp only [remainingGoodConstant, sub_zero, add_zero, ←Real.sqrt_eq_rpow]
  apply le_trans _ hh
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  have hi0 := (cappedRepresentative_pos i).le
  have hj0 := (cappedRepresentative_pos j).le
  have hκ : 1≤(1+φ/cappedRepresentative j)^(1/4:ℝ) :=
    Real.one_le_rpow (by linarith [div_nonneg hφ.le hj0]) (by norm_num)
  rw [mul_comm _ (φ/(cappedRepresentative i)^2)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact le_mul_of_one_le_right (by positivity) hκ

lemma remaining_large_good_angles_expanded (Sφ : Finset ℕ) (Sθ : ℕ→Finset ℕ) (Sσ : ℕ→ℕ→Finset ℕ)
    (hθ : ∀nf∈Sφ,∀i∈Sθ nf,cappedRepresentative nf≤16384*cappedRepresentative i)
    (hσ : ∀nf∈Sφ,∀i∈Sθ nf,∀j∈Sσ nf i,cappedRepresentative j≤131080*cappedRepresentative i) :
    (∑nf∈Sφ,∑i∈Sθ nf,∑j∈Sσ nf i,(min (cappedRepresentative i) (cappedRepresentative j))^(3/2:ℝ)*
      (cappedRepresentative nf/(cappedRepresentative i)^2))≤
      remainingGoodConstant 131080 16384 0*directDyadicPowerConstant (1/2) := by
  calc
    _≤∑nf∈Sφ,remainingGoodConstant 131080 16384 0*Real.sqrt (cappedRepresentative nf) :=
      Finset.sum_le_sum (fun nf hnf=>remaining_large_good_receiver_expanded (cappedRepresentative_pos nf)
        (Sθ nf) (Sσ nf) (hθ nf hnf) (hσ nf hnf))
    _≤_ := by
      rw [←Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ (remainingGoodConstant_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      have hh := capped_positive_power_sum_unscaled (by norm_num : (0:ℝ)<1)
        (by norm_num : (0:ℝ)<1/2) Sφ (fun n _=>cappedRepresentative_le_one n)
      simpa only [directDyadicPowerConstant,Real.one_rpow,mul_one,←Real.sqrt_eq_rpow,Real.sqrt_one] using hh

lemma remaining_large_magnetic_receiver_expanded {φ : ℝ} (hφ : 0≤φ)
    (Sθ : Finset ℕ) (Sσ : ℕ→Finset ℕ)
    (hσ : ∀i∈Sθ,∀j∈Sσ i,cappedRepresentative j≤131080*cappedRepresentative i) :
    (∑i∈Sθ,∑j∈Sσ i,(min (cappedRepresentative i) (cappedRepresentative j))^(4/3:ℝ)*
      (cappedRepresentative i)^(-(2/3:ℝ))*φ^(1/3:ℝ))≤
      directDyadicPowerConstant (4/3)*(131080:ℝ)^(4/3:ℝ)*directDyadicPowerConstant (2/3)*φ^(1/3:ℝ) := by
  have hh := capped_positive_power_sum_unscaled (by norm_num : (0:ℝ)<1)
    (by norm_num : (0:ℝ)<2/3) Sθ (fun n _=>cappedRepresentative_le_one n)
  rw [Real.one_rpow,mul_one] at hh
  have hC : 0≤directDyadicPowerConstant (4/3)*(131080:ℝ)^(4/3:ℝ) :=
    mul_nonneg (directDyadicPowerConstant_nonneg (by norm_num)) (by positivity)
  calc
    _≤∑i∈Sθ,directDyadicPowerConstant (4/3)*(131080:ℝ)^(4/3:ℝ)*(cappedRepresentative i)^(2/3:ℝ)*φ^(1/3:ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      simpa only [one_mul,mul_one,directDyadicPowerConstant] using large_radius_magnetic_relative_sum
        (by norm_num : (0:ℝ)≤1) (cappedRepresentative_pos i) hφ (by norm_num : (0:ℝ)<131080) (Sσ i) (hσ i hi)
    _=(directDyadicPowerConstant (4/3)*(131080:ℝ)^(4/3:ℝ))*(∑i∈Sθ,(cappedRepresentative i)^(2/3:ℝ))*φ^(1/3:ℝ) := by
      simp only [Finset.sum_mul,Finset.mul_sum]
    _≤_ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh hC) (Real.rpow_nonneg hφ _)

lemma remaining_large_magnetic_angles_expanded (Sφ : Finset ℕ) (Sθ : ℕ→Finset ℕ) (Sσ : ℕ→ℕ→Finset ℕ)
    (hσ : ∀nf∈Sφ,∀i∈Sθ nf,∀j∈Sσ nf i,cappedRepresentative j≤131080*cappedRepresentative i) :
    (∑nf∈Sφ,∑i∈Sθ nf,∑j∈Sσ nf i,(min (cappedRepresentative i) (cappedRepresentative j))^(4/3:ℝ)*
      (cappedRepresentative i)^(-(2/3:ℝ))*(cappedRepresentative nf)^(1/3:ℝ))≤
      directDyadicPowerConstant (4/3)*(131080:ℝ)^(4/3:ℝ)*directDyadicPowerConstant (2/3)*directDyadicPowerConstant (1/3) := by
  calc
    _≤∑nf∈Sφ,directDyadicPowerConstant (4/3)*(131080:ℝ)^(4/3:ℝ)*directDyadicPowerConstant (2/3)*
        (cappedRepresentative nf)^(1/3:ℝ) :=
      Finset.sum_le_sum (fun nf hnf=>remaining_large_magnetic_receiver_expanded (cappedRepresentative_pos nf).le
        (Sθ nf) (Sσ nf) (hσ nf hnf))
    _≤_ := by
      rw [←Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ (by
        exact mul_nonneg (mul_nonneg (directDyadicPowerConstant_nonneg (by norm_num)) (by positivity)) (directDyadicPowerConstant_nonneg (by norm_num)))
      have hh := capped_positive_power_sum_unscaled (by norm_num : (0:ℝ)<1)
        (by norm_num : (0:ℝ)<1/3) Sφ (fun n _=>cappedRepresentative_le_one n)
      simpa only [directDyadicPowerConstant,Real.one_rpow,mul_one] using hh

lemma remaining_large_combined_angles_expanded {g b : ℝ} (hg : 0≤g) (hb : 0≤b)
    (Sφ : Finset ℕ) (Sθ : ℕ→Finset ℕ) (Sσ : ℕ→ℕ→Finset ℕ)
    (hθ : ∀nf∈Sφ,∀i∈Sθ nf,cappedRepresentative nf≤16384*cappedRepresentative i)
    (hσ : ∀nf∈Sφ,∀i∈Sθ nf,∀j∈Sσ nf i,cappedRepresentative j≤131080*cappedRepresentative i) :
    (∑nf∈Sφ,∑i∈Sθ nf,∑j∈Sσ nf i,
      (g*(min (cappedRepresentative i) (cappedRepresentative j))^(3/2:ℝ)*
        (cappedRepresentative nf/(cappedRepresentative i)^2)+
       b*(min (cappedRepresentative i) (cappedRepresentative j))^(4/3:ℝ)*
        (cappedRepresentative i)^(-(2/3:ℝ))*(cappedRepresentative nf)^(1/3:ℝ)))≤
      g*(remainingGoodConstant 131080 16384 0*directDyadicPowerConstant (1/2))+
      b*(directDyadicPowerConstant (4/3)*(131080:ℝ)^(4/3:ℝ)*directDyadicPowerConstant (2/3)*directDyadicPowerConstant (1/3)) := by
  have hg' := remaining_large_good_angles_expanded Sφ Sθ Sσ hθ hσ
  have hb' := remaining_large_magnetic_angles_expanded Sφ Sθ Sσ hσ
  simp_rw [mul_assoc, Finset.sum_add_distrib, ←Finset.mul_sum]
  simpa only [mul_assoc] using add_le_add (mul_le_mul_of_nonneg_left hg' hg) (mul_le_mul_of_nonneg_left hb' hb)

end RVM

end

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

namespace RVM

lemma Admissible.direct_remaining_source_large_uniform_expanded {d : Datum} (hd : Admissible d) :
    ∃C : ℝ,0≤C ∧ ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T →
    ∀ (zX : Phase) (S : Set Phase) (a b I w P : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0≤a → b≤T → b-a≤I → 0<I → I≤1 → 0≤P →
    ∀ (Sp Sφ : Finset ℕ) (Sθ : ℕ→ℕ→Finset ℕ) (Sσ : ℕ→ℕ→ℕ→Finset ℕ),
      (∀np∈Sp,sourceRepresentative np≤128*P) →
      (∀np∈Sp,∀nf∈Sφ,∀nt∈Sθ np nf,cappedRepresentative nf≤16384*cappedRepresentative nt) →
      (∀np∈Sp,∀nf∈Sφ,∀nt∈Sθ np nf,∀j∈Sσ np nf nt,cappedRepresentative j≤131080*cappedRepresentative nt) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := fun np nt nf j nr=>relativeRepresentativeClosedBin T w ![np,nt,nf,nr] j
      (∑np∈Sp,∑nf∈Sφ,∑nt∈Sθ np nf,∑j∈Sσ np nf nt,∑'nr : ℕ,
        if I ≤ max 1 T*cappedRepresentative nr then
          ∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V (B np nt nf j nr) z
            ∂physicalBinMeasure V (B np nt nf j nr) (Icc a b) else 0)≤
      ENNReal.ofReal (C*(P*Real.sqrt I)) := by
  obtain ⟨Cg,Cb,hCg,hCb,hbin⟩ := hd.direct_source_large_sharp_sum
  let E := datumEnergyNumber d
  let Kg := relativeCauchyConstant Cg E (20*E)
  let Kb := relativeCauchyConstant Cb E (120*E)
  let Dg := dyadicBalanceConstant (1/2) (1/2)
  let Db := dyadicBalanceConstant 1 (1/2)
  let Ag := remainingGoodConstant 131080 16384 0*directDyadicPowerConstant (1/2)
  let Ab := directDyadicPowerConstant (4/3)*(131080:ℝ)^(4/3:ℝ)*directDyadicPowerConstant (2/3)*directDyadicPowerConstant (1/3)
  have hKg : 0≤Kg := relativeCauchyConstant_nonneg hCg
  have hKb : 0≤Kb := relativeCauchyConstant_nonneg hCb
  have hDg : 0≤Dg := (dyadicBalanceConstant_pos (by norm_num) (by norm_num)).le
  have hDb : 0≤Db := (dyadicBalanceConstant_pos (by norm_num) (by norm_num)).le
  have hAg : 0≤Ag := mul_nonneg
    (remainingGoodConstant_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (directDyadicPowerConstant_nonneg (by norm_num))
  have hAb : 0≤Ab := by
    dsimp [Ab]
    exact mul_nonneg (mul_nonneg (mul_nonneg (directDyadicPowerConstant_nonneg (by norm_num))
      (by positivity)) (directDyadicPowerConstant_nonneg (by norm_num))) (directDyadicPowerConstant_nonneg (by norm_num))
  refine ⟨256*(Kg*Dg*Ag+Kb*Db*Ab),by positivity,?_⟩
  intro s T F hs hT zX S a b I w P hS hS0 ha hb hJI hI hI1 hP Sp Sφ Sθ Sσ hp hθ hσ
  dsimp only
  let g (np : ℕ) := Kg*Dg*(I : ℝ)^(3/4:ℝ)*sourceRepresentative np
  let b' (np : ℕ) := Kb*Real.sqrt I*Db*sourceRepresentative np
  let f (np nf nt j : ℕ) :=
    g np*(min (cappedRepresentative nt) (cappedRepresentative j))^(3/2:ℝ)*
      (cappedRepresentative nf/(cappedRepresentative nt)^2)+
    b' np*(min (cappedRepresentative nt) (cappedRepresentative j))^(4/3:ℝ)*
      (cappedRepresentative nt)^(-(2/3:ℝ))*(cappedRepresentative nf)^(1/3:ℝ)
  have hgn (np : ℕ) : 0≤g np := by dsimp [g,sourceRepresentative]; positivity
  have hbn (np : ℕ) : 0≤b' np := by dsimp [b',sourceRepresentative]; positivity
  have hfn (np nf nt j : ℕ) : 0≤f np nf nt j := by
    have hnt := (cappedRepresentative_pos nt).le
    have hnf := (cappedRepresentative_pos nf).le
    have hj := (cappedRepresentative_pos j).le
    have hg0 := hgn np
    have hb0 := hbn np
    dsimp [f]
    positivity
  calc
    _≤∑np∈Sp,∑nf∈Sφ,∑nt∈Sθ np nf,∑j∈Sσ np nf nt,ENNReal.ofReal (f np nf nt j) := by
      apply Finset.sum_le_sum
      intro np hnp
      apply Finset.sum_le_sum
      intro nf hnf
      apply Finset.sum_le_sum
      intro nt hnt
      apply Finset.sum_le_sum
      intro j hj
      have hh := hbin s T F hs.energyPrefix hT hs.initial_f zX S np nt nf j a b I w hS hS0 ha hb hJI hI
      dsimp only at hh
      rw [hs.initial_energy_eq] at hh
      apply hh.trans_eq
      congr 1
      dsimp [f,g,b',Kg,Kb,Dg,Db,E]
      ring
    _=ENNReal.ofReal (∑np∈Sp,∑nf∈Sφ,∑nt∈Sθ np nf,∑j∈Sσ np nf nt,f np nf nt j) := by
      simp_rw [←ENNReal.ofReal_sum_of_nonneg (fun j _=>hfn _ _ _ j),
        ←ENNReal.ofReal_sum_of_nonneg (fun n _=>Finset.sum_nonneg (fun j _=>hfn _ _ n j)),
        ←ENNReal.ofReal_sum_of_nonneg (fun n _=>Finset.sum_nonneg (fun j _=>Finset.sum_nonneg (fun k _=>hfn _ n j k))),
        ←ENNReal.ofReal_sum_of_nonneg (fun n _=>Finset.sum_nonneg (fun j _=>Finset.sum_nonneg (fun k _=>Finset.sum_nonneg (fun l _=>hfn n j k l))))]
    _≤ENNReal.ofReal (∑np∈Sp,(g np*Ag+b' np*Ab)) := by
      apply ENNReal.ofReal_le_ofReal
      apply Finset.sum_le_sum
      intro np hnp
      exact remaining_large_combined_angles_expanded (hgn np) (hbn np) Sφ (Sθ np) (Sσ np) (hθ np hnp) (hσ np hnp)
    _≤_ := by
      apply ENNReal.ofReal_le_ofReal
      have hsump := sourceRepresentative_sum_bound (by positivity : 0≤128*P) Sp hp
      have hIpow := rpow_three_quarters_le_sqrt hI hI1
      have hs' : ∑np∈Sp,(g np*Ag+b' np*Ab)≤
          (Kg*Dg*Ag+Kb*Db*Ab)*Real.sqrt I*(∑np∈Sp,sourceRepresentative np) := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro np hnp
        have hpp : 0 ≤ sourceRepresentative np := by dsimp [sourceRepresentative]; positivity
        dsimp [g,b']
        nlinarith [mul_le_mul_of_nonneg_left hIpow (mul_nonneg (mul_nonneg (mul_nonneg hKg hDg) hAg) hpp)]
      apply hs'.trans
      calc
        _≤(Kg*Dg*Ag+Kb*Db*Ab)*Real.sqrt I*(2*(128*P)) := mul_le_mul_of_nonneg_left hsump (by positivity)
        _=_ := by ring

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_DirectExpandedAssemble
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

namespace RVM

lemma ennreal_sum_subset_bound {α : Type*} {s t : Finset α} {f g : α→ℝ≥0∞}
    (hst : s⊆t) (hfg : ∀x∈s,f x≤g x) : (∑x∈s,f x)≤∑x∈t,g x :=
  (Finset.sum_le_sum hfg).trans
    (Finset.sum_le_sum_of_subset_of_nonneg hst (fun _ _ _=>bot_le))

lemma ennreal_radius_split (f : ℕ→ℝ≥0∞) (r : ℕ→ℝ) (I : ℝ) :
    (∑'n,f n)≤(∑'n,if r n≤I then f n else 0)+(∑'n,if I ≤ r n then f n else 0) := by
  rw [←ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro n
  by_cases h : r n≤I
  · simp only [ite_eq_left h]
    exact le_add_right le_rfl
  · simp [h,(not_le.mp h).le]

lemma Admissible.direct_remaining_source_complete_uniform_oai {d : Datum} (hd : Admissible d) :
    ∃C : ℝ,0≤C ∧ ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T →
    ∀ (zX : Phase) (S : Set Phase) (a b I w M A P K : ℝ) (N : ℕ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0≤a → b≤T → a≤b → 0<I → I≤1 → b-a≤I →
      1≤M → 1≤A → 1≤P → 1≤Real.log (2+P) → 0<w → w≤P →
      I≤(w/P)^2 → 0≤K → (N:ℝ)≤K*Real.log (2+P) →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := fun np nf nt j nr=>relativeRepresentativeClosedBin T w ![np,nt,nf,nr] j
      let Sp := (Finset.range N).filter (fun np=>sourceRepresentative np≤128*P)
      let Sf := (Finset.range N).filter (fun nf=>1/(32*w) ≤ cappedRepresentative nf)
      let St := fun nf=>(Finset.range N).filter (fun nt=>cappedRepresentative nf≤16384*cappedRepresentative nt)
      let Ss := fun nt=>(Finset.range N).filter (fun j=>cappedRepresentative j≤131080*cappedRepresentative nt)
      (∑np∈Sp,∑nf∈Sf,∑nt∈St nf,∑j∈Ss nt,∑'nr : ℕ,
        ∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V (B np nf nt j nr) z
          ∂physicalBinMeasure V (B np nf nt j nr) (Icc a b))≤
      ENNReal.ofReal (C*(1+K^4)*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w)) := by
  obtain ⟨Ch,hCh,hhigh⟩ := hd.direct_remaining_source_short_uniform_expanded
  obtain ⟨Cl,hCl,hlow⟩ := hd.direct_remaining_source_deficit_short_uniform_expanded
  obtain ⟨Cb,hCb,hlarge⟩ := hd.direct_remaining_source_large_uniform_expanded
  refine ⟨Ch+Cl+Cb,by positivity,?_⟩
  intro s T F hs hT zX S a b I w M A P K N hS hS0 ha hb hab hI hI1 hJI hM hA hP hL hw hwP hIP hK hN HX HZ
  dsimp only
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  let B := fun np nf nt j nr=>relativeRepresentativeClosedBin T w ![np,nt,nf,nr] j
  let f := fun np nf nt j nr=>∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V (B np nf nt j nr) z
    ∂physicalBinMeasure V (B np nf nt j nr) (Icc a b)
  let r := fun nr=>max 1 T*cappedRepresentative nr
  let D := fun np nf nt j=>∑'nr,if r nr≤I then f np nf nt j nr else 0
  let L := fun np nf nt j=>∑'nr,if I ≤ r nr then f np nf nt j nr else 0
  let Sp := (Finset.range N).filter (fun np=>sourceRepresentative np≤128*P)
  let Sf := (Finset.range N).filter (fun nf=>1/(32*w) ≤ cappedRepresentative nf)
  let St := fun nf=>(Finset.range N).filter (fun nt=>cappedRepresentative nf≤16384*cappedRepresentative nt)
  let Ss := fun nt=>(Finset.range N).filter (fun j=>cappedRepresentative j≤131080*cappedRepresentative nt)
  let hi := fun np j=>512 ≤ cappedRepresentative j*sourceRepresentative np ∧ 32 ≤ cappedRepresentative j*w
  let lo := fun np j=>cappedRepresentative j*sourceRepresentative np≤512 ∨ cappedRepresentative j*w≤32
  let Sh := fun np nt=>(Ss nt).filter (fun j=>hi np j)
  let R := P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w
  have hR : P*Real.sqrt I≤R := le_add_of_nonneg_right (by positivity)
  have hR0 : 0≤R := by dsimp [R]; positivity
  have hp (np : ℕ) (hnp : np∈Sp) : sourceRepresentative np≤128*P := (Finset.mem_filter.mp hnp).2
  have hf (nf : ℕ) (hnf : nf∈Sf) : 1/(32*w) ≤ cappedRepresentative nf := (Finset.mem_filter.mp hnf).2
  have ht (nf nt : ℕ) (hnt : nt∈St nf) : cappedRepresentative nf≤16384*cappedRepresentative nt := (Finset.mem_filter.mp hnt).2
  have hj (nt j : ℕ) (hj : j∈Ss nt) : cappedRepresentative j≤131080*cappedRepresentative nt := (Finset.mem_filter.mp hj).2
  have hhigh' := hhigh s T F hs hT zX S a b I w M A P hS hS0 ha hb hab hI hI1 hJI hM hA hP hL hw hwP HX HZ
    Sp Sf (fun _ nf=>St nf) (fun np _ nt=>Sh np nt) hp hf (fun _ _ nf _ nt hnt=>ht nf nt hnt)
    (fun np _ _ _ nt _ j hj'=>⟨hj nt j (Finset.mem_filter.mp hj').1,(Finset.mem_filter.mp hj').2⟩)
  have hlarge' := hlarge s T F hs hT zX S a b I w P hS hS0 ha hb hJI hI hI1 (by positivity)
    Sp Sf (fun _ nf=>St nf) (fun _ _ nt=>Ss nt) hp (fun _ _ nf _ nt hnt=>ht nf nt hnt)
    (fun _ _ _ _ nt _ j hj'=>hj nt j hj')
  have hlow' := hlow s T F hs hT zX S a b I w P K N hS hS0 ha hb hJI hI hI1 hw hP hIP hK hN
  have hlo : (∑np∈Sp,∑nf∈Sf,∑nt∈St nf,∑j∈Ss nt,if lo np j then D np nf nt j else 0)≤
      ENNReal.ofReal (Cl*K^4*(P*Real.sqrt I)) := by
    apply le_trans _ hlow'
    apply ennreal_sum_subset_bound (Finset.filter_subset _ _)
    intro np hnp
    apply ennreal_sum_subset_bound (Finset.filter_subset _ _)
    intro nf hnf
    apply ennreal_sum_subset_bound (Finset.filter_subset _ _)
    intro nt hnt
    apply ennreal_sum_subset_bound (Finset.filter_subset _ _)
    intro j hj'
    simp only [hp np hnp,ht nf nt hnt,true_and]
    exact le_rfl
  have hpoint (np nf nt j : ℕ) : (∑'nr,f np nf nt j nr)≤
      (if hi np j then D np nf nt j else 0)+(if lo np j then D np nf nt j else 0)+L np nf nt j := by
    apply (ennreal_radius_split (f np nf nt j) r I).trans
    apply add_le_add _ le_rfl
    by_cases hl : lo np j
    · simp only [ite_eq_left hl]
      exact le_add_left le_rfl
    · have hh : hi np j := by
        dsimp [lo] at hl
        push Not at hl
        exact ⟨hl.1.le,hl.2.le⟩
      simp only [ite_eq_left hh,ite_eq_right hl,add_zero]
      exact le_rfl
  change (∑np∈Sp,∑nf∈Sf,∑nt∈St nf,∑j∈Ss nt,∑'nr,f np nf nt j nr)≤_
  calc
    _≤∑np∈Sp,∑nf∈Sf,∑nt∈St nf,∑j∈Ss nt,
        ((if hi np j then D np nf nt j else 0)+(if lo np j then D np nf nt j else 0)+L np nf nt j) :=
      Finset.sum_le_sum (fun np _=>Finset.sum_le_sum (fun nf _=>Finset.sum_le_sum
        (fun nt _=>Finset.sum_le_sum (fun j _=>hpoint np nf nt j))))
    _=(∑np∈Sp,∑nf∈Sf,∑nt∈St nf,∑j∈Sh np nt,D np nf nt j)+
        (∑np∈Sp,∑nf∈Sf,∑nt∈St nf,∑j∈Ss nt,if lo np j then D np nf nt j else 0)+
        (∑np∈Sp,∑nf∈Sf,∑nt∈St nf,∑j∈Ss nt,L np nf nt j) := by
      simp only [Sh,Finset.sum_filter,Finset.sum_add_distrib]
    _≤ENNReal.ofReal (Ch*R)+ENNReal.ofReal (Cl*K^4*(P*Real.sqrt I))+ENNReal.ofReal (Cb*(P*Real.sqrt I)) :=
      add_le_add (add_le_add hhigh' hlo) hlarge'
    _≤ENNReal.ofReal (Ch*R+Cl*K^4*R+Cb*R) := by
      rw [ENNReal.ofReal_add (by positivity : 0≤Ch*R+Cl*K^4*R) (by positivity),
        ENNReal.ofReal_add (by positivity : 0≤Ch*R) (by positivity)]
      exact add_le_add (add_le_add le_rfl (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hR (by positivity))))
        (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hR hCb))
    _≤_ := by
      apply ENNReal.ofReal_le_ofReal
      have hc : Ch+Cl*K^4+Cb≤(Ch+Cl+Cb)*(1+K^4) := by
        nlinarith [mul_nonneg hCh (pow_nonneg hK 4),mul_nonneg hCb (pow_nonneg hK 4)]
      calc
        _=(Ch+Cl*K^4+Cb)*R := by ring
        _≤_ := mul_le_mul_of_nonneg_right hc hR0

end RVM

end

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

end

end OAI
end

theorem solution : type_of% @OAI.RVM.Admissible.direct_remaining_source_complete_uniform_oai := @OAI.RVM.Admissible.direct_remaining_source_complete_uniform_oai
