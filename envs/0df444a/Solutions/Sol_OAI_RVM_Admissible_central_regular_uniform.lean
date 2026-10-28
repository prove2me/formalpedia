-- Prove2me | solution 1 for OAI.RVM.Admissible.central_regular_uniform
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:36:48.836852+00:00
-- url     : https://prove2.me/submissions/93791c1e-0099-43c2-a1ae-592b0e0d92e0

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000
import Theorems.Thm_OAI_RVM_Admissible_representative_regular_central_shared
import Theorems.Thm_OAI_RVM_SmoothClassicalPrefix_representativeJointEnergy_sum

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

end RVM

end

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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Flow_ClosedEulerianCrudeBudget
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

lemma geometry_radial_balance {I R p θ φ H : ℝ}
    (hI : 0<I) (hR : 0<R) (hp : 0<p) (hθ : 0<θ) (hφ : 0<φ) (hH : 0<H) :
    Summable (fun k : ℤ=>min (I*p^3*θ*φ^4*(H*(2:ℝ)^k))
      (R^2/(p*θ*(H*(2:ℝ)^k)))) ∧
    (∑'k : ℤ,min (I*p^3*θ*φ^4*(H*(2:ℝ)^k))
      (R^2/(p*θ*(H*(2:ℝ)^k)))) ≤ 6*Real.sqrt I*R*p*φ^2 := by
  let a := I*p^3*θ*φ^4*H
  let b := R^2/(p*θ*H)
  let r := R/(Real.sqrt I*p^2*θ*φ^2*H)
  have ha : 0<a := by dsimp [a]; positivity
  have hb : 0<b := by dsimp [b]; positivity
  have hr : 0 < r := by dsimp [r]; positivity
  have he (k : ℤ) : min (a*((2:ℝ)^k)^(1:ℝ)) (b*((2:ℝ)^k)^(-(1:ℝ)))=
      min (I*p^3*θ*φ^4*(H*(2:ℝ)^k)) (R^2/(p*θ*(H*(2:ℝ)^k))) := by
    rw [Real.rpow_one,Real.rpow_neg_one]
    dsimp [a,b]
    congr 1 <;> ring
  have hs := dyadic_power_min_summable ha.le hb.le (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<1)
  have ht := dyadic_balance_at ha.le hb.le (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<1) hr
  simp_rw [he] at hs ht
  refine ⟨hs,ht.trans_eq ?_⟩
  norm_num only [Real.rpow_one,Real.rpow_neg_one]
  dsimp [a,b,r]
  have hsqrt : (Real.sqrt I)^2=I := Real.sq_sqrt hI.le
  have hs0 : Real.sqrt I≠0 := (Real.sqrt_pos.mpr hI).ne'
  field_simp
  nlinarith [hsqrt]

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

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_IndexTwoPow
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

lemma index_lt_of_two_pow_le {n N : ℕ} {B : ℝ}
    (hn : (2:ℝ)^n ≤ B) (hN : B < (2:ℝ)^N) : n<N := by
  by_contra hc
  have he := pow_le_pow_right₀ (show (1:ℝ)≤2 by norm_num) (Nat.le_of_not_gt hc)
  exact (not_lt_of_ge (he.trans hn)) hN

end RVM

open Set

namespace RVM

lemma exists_dyadic_count_log {B : ℝ} (hB : 1 ≤ B) :
    ∃N : ℕ, B < (2:ℝ)^N ∧ (N:ℝ) ≤ 2+Real.log B/Real.log 2 := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h0 : 0 ≤ Real.log B/Real.log 2 := div_nonneg (Real.log_nonneg hB) h2.le
  let n := ⌈Real.log B/Real.log 2⌉₊
  refine ⟨n+1,?_,?_⟩
  · apply (Real.log_lt_log_iff (zero_lt_one.trans_le hB) (by positivity)).mp
    rw [Real.log_pow,Nat.cast_add,Nat.cast_one]
    have hc : Real.log B/Real.log 2 < (n:ℝ)+1 := by
      have hh := Nat.le_ceil (Real.log B/Real.log 2)
      dsimp [n]
      linarith only [hh]
    exact (div_lt_iff₀ h2).mp hc
  · have hh : (n:ℝ) < Real.log B/Real.log 2+1 := Nat.ceil_lt_add_one h0
    push_cast
    linarith only [hh]

end RVM

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


lemma Admissible.datumEnergyNumber_nonneg {d : Datum} (hd : Admissible d) :
    0≤datumEnergyNumber d := by
  apply integral_nonneg
  intro x
  apply add_nonneg (by positivity)
  exact integral_nonneg (fun v=>mul_nonneg (q_pos v).le (hd.2.2.1 _))

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_SelectionCounts
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

lemma sourceRepresentative_two_pow (n : ℕ) : sourceRepresentative n=(2:ℝ)^(n+6) := by
  simp only [sourceRepresentative,pow_add]
  ring

lemma selection_angle_index {np nt : ℕ}
    (h : 1/sourceRepresentative np ≤ cappedRepresentative nt) : nt≤np+6 := by
  rw [sourceRepresentative_two_pow] at h
  have he : (2:ℝ)^nt≤2^(np+6) := by
    have hp : 0<(2:ℝ)^nt := by positivity
    have hq : 0<(2:ℝ)^(np+6) := by positivity
    dsimp [cappedRepresentative] at h
    rw [inv_pow,one_div] at h
    exact (inv_le_inv₀ hq hp).mp h
  exact (pow_le_pow_iff_right₀ (by norm_num : (1:ℝ)<2)).mp he

lemma source_ratio_sq_le {p w : ℝ} (hp : 0<p) (_ : 0<w) :
    (p/min p w)^2≤1+(p/w)^2 := by
  rcases le_total p w with h|h
  · rw [min_eq_left h,div_self hp.ne',one_pow]
    linarith [sq_nonneg (p/w)]
  · rw [min_eq_right h]
    linarith

lemma source_ratio_sq_sum {P w : ℝ} (hP : 0≤P) (hw : 0<w) (S : Finset ℕ)
    (hS : ∀n∈S,sourceRepresentative n≤P) :
    ∑n∈S,(sourceRepresentative n/min (sourceRepresentative n) w)^2≤
      (S.card:ℝ)+2*(P/w)^2 := by
  have hp (n : ℕ) : 0 < sourceRepresentative n := by dsimp [sourceRepresentative]; positivity
  calc
    _≤∑n∈S,(1+(sourceRepresentative n/w)^2) :=
      Finset.sum_le_sum (fun n _=>source_ratio_sq_le (hp n) hw)
    _=(S.card:ℝ)+(∑n∈S,(sourceRepresentative n)^2)/w^2 := by
      simp_rw [Finset.sum_add_distrib,div_pow,←Finset.sum_div]
      simp
    _≤(S.card:ℝ)+(2*P^2)/w^2 := by
      gcongr
      calc
        _≤∑n∈S,P*sourceRepresentative n := Finset.sum_le_sum (fun n hn=>by
          nlinarith [mul_le_mul_of_nonneg_right (hS n hn) (hp n).le])
        _=P*(∑n∈S,sourceRepresentative n) := (Finset.mul_sum ..).symm
        _≤P*(2*P) := mul_le_mul_of_nonneg_left (sourceRepresentative_sum_bound hP S hS) hP
        _=2*P^2 := by ring
    _=_ := by ring

lemma pair_source_ratio_sq_sum {P w N : ℝ} (hP : 0≤P) (hw : 0<w)
    (S : Finset (ℕ×ℕ)) (hS : ∀n∈S,sourceRepresentative n.1≤P)
    (hpN : ((S.image Prod.fst).card:ℝ)≤N) (hfN : ((S.image Prod.snd).card:ℝ)≤N) :
    (∑n∈S,(sourceRepresentative n.1/min (sourceRepresentative n.1) w)^2)≤
      N*(N+2*(P/w)^2) ∧
    (∑n∈S,(sourceRepresentative n.1/min (sourceRepresentative n.1) w)^2*cappedRepresentative n.2)≤
      2*(N+2*(P/w)^2) := by
  classical
  let U := S.image Prod.fst
  let V := S.image Prod.snd
  have hN : 0≤N := (Nat.cast_nonneg U.card).trans hpN
  have hU (n) (hn : n∈U) : sourceRepresentative n≤P := by
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hn
    exact hS k hk
  have hsub : S⊆U.product V := by
    intro n hn
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨n,hn,rfl⟩,Finset.mem_image.mpr ⟨n,hn,rfl⟩⟩
  have hu : (∑n∈U,(sourceRepresentative n/min (sourceRepresentative n) w)^2)≤N+2*(P/w)^2 :=
    (source_ratio_sq_sum hP hw U hU).trans (by gcongr)
  have hv : ∑n∈V,cappedRepresentative n≤2 := by
    have hh := capped_positive_power_sum_unscaled (by norm_num : (0:ℝ)<1)
      (by norm_num : (0:ℝ)<1) V (fun n _=>cappedRepresentative_le_one n)
    norm_num at hh
    exact hh
  constructor
  · calc
      _≤∑n∈U.product V,(sourceRepresentative n.1/min (sourceRepresentative n.1) w)^2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _=>sq_nonneg _)
      _=(∑n∈U,(sourceRepresentative n/min (sourceRepresentative n) w)^2)*(V.card:ℝ) := by
        simp only [Finset.product_eq_sprod,Finset.sum_product,Finset.sum_const,nsmul_eq_mul]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro n hn
        ring
      _≤(N+2*(P/w)^2)*N := mul_le_mul hu hfN (Nat.cast_nonneg _) (by positivity)
      _=_ := by ring
  · calc
      _≤∑n∈U.product V,(sourceRepresentative n.1/min (sourceRepresentative n.1) w)^2*cappedRepresentative n.2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _=>mul_nonneg (sq_nonneg _) (cappedRepresentative_pos _).le)
      _=(∑n∈U,(sourceRepresentative n/min (sourceRepresentative n) w)^2)*(∑n∈V,cappedRepresentative n) := by
        rw [Finset.product_eq_sprod,Finset.sum_product]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro n hn
        rw [Finset.mul_sum]
      _≤(N+2*(P/w)^2)*2 := mul_le_mul hu hv (Finset.sum_nonneg (fun n _=>(cappedRepresentative_pos n).le)) (by positivity)
      _=_ := by ring

lemma joint_budget_Cauchy {E N x : ℝ} (hE : 0≤E) (hN : 0≤N) (hx : 0≤x)
    {ι : Type*} (S : Finset ι) (J W : ι→ℝ) (hJ : ∀i∈S,0≤J i)
    (hbudget : ∑i∈S,J i≤E) (hW : ∑i∈S,(W i)^2≤N*(N+2*x^2)) :
    ∑i∈S,W i*Real.sqrt (J i)≤Real.sqrt E*(N+2*Real.sqrt N*x) := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq S W (fun i=>Real.sqrt (J i))
  have he : (∑i∈S,(Real.sqrt (J i))^2)=∑i∈S,J i :=
    Finset.sum_congr rfl (fun i hi=>Real.sq_sqrt (hJ i hi))
  rw [he] at hc
  have hu := mul_le_mul hW hbudget (Finset.sum_nonneg hJ) (by positivity : 0≤N*(N+2*x^2))
  have hs := Real.sq_sqrt hE
  have hn := Real.sq_sqrt hN
  have hb : 0≤Real.sqrt E*(N+2*Real.sqrt N*x) := by positivity
  have hsq : N*(N+2*x^2)*E≤(Real.sqrt E*(N+2*Real.sqrt N*x))^2 := by
    rw [mul_pow,hs]
    have he : (N+2*Real.sqrt N*x)^2=N^2+4*N*Real.sqrt N*x+4*N*x^2 := by
      ring_nf
      rw [hn]
      ring
    rw [he]
    nlinarith [mul_nonneg hE (mul_nonneg hN (mul_nonneg (Real.sqrt_nonneg N) hx)),
      mul_nonneg hE (mul_nonneg hN (sq_nonneg x))]
  exact le_of_sq_le_sq (hc.trans (hu.trans hsq)) hb

lemma joint_budget_weighted_Cauchy {E N x : ℝ} (hE : 0≤E) (hN : 0≤N) (hx : 0≤x)
    {ι : Type*} (S : Finset ι) (J W : ι→ℝ) (hJ : ∀i∈S,0≤J i)
    (hbudget : ∑i∈S,J i≤E) (hW : ∑i∈S,(W i)^2≤2*(N+2*x^2)) :
    ∑i∈S,W i*Real.sqrt (J i)≤Real.sqrt E*(2*Real.sqrt N+2*x) := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq S W (fun i=>Real.sqrt (J i))
  have he : (∑i∈S,(Real.sqrt (J i))^2)=∑i∈S,J i :=
    Finset.sum_congr rfl (fun i hi=>Real.sq_sqrt (hJ i hi))
  rw [he] at hc
  have hu := mul_le_mul hW hbudget (Finset.sum_nonneg hJ) (by positivity : 0≤2*(N+2*x^2))
  have hs := Real.sq_sqrt hE
  have hn := Real.sq_sqrt hN
  have hb : 0≤Real.sqrt E*(2*Real.sqrt N+2*x) := by positivity
  have hsq : 2*(N+2*x^2)*E≤(Real.sqrt E*(2*Real.sqrt N+2*x))^2 := by
    rw [mul_pow,hs]
    have he : (2*Real.sqrt N+2*x)^2=4*N+8*Real.sqrt N*x+4*x^2 := by
      ring_nf
      rw [hn]
      ring
    rw [he]
    nlinarith [mul_nonneg hE (mul_nonneg (Real.sqrt_nonneg N) hx),mul_nonneg hE hN]
  exact le_of_sq_le_sq (hc.trans (hu.trans hsq)) hb

lemma shared_weighted_pair_Cauchy {P w N E : ℝ} (hP : 0≤P) (hw : 0<w) (hE : 0≤E)
    (S : Finset (ℕ×ℕ)) (J : ℕ×ℕ→ℝ) (hJ : ∀n∈S,0≤J n)
    (hbudget : ∑n∈S,J n≤E) (hS : ∀n∈S,sourceRepresentative n.1≤P)
    (hpN : ((S.image Prod.fst).card:ℝ)≤N) (hfN : ((S.image Prod.snd).card:ℝ)≤N) :
    (∑n∈S,(sourceRepresentative n.1/min (sourceRepresentative n.1) w)*Real.sqrt (J n))≤
      Real.sqrt E*(N+2*Real.sqrt N*(P/w)) ∧
    (∑n∈S,(sourceRepresentative n.1/min (sourceRepresentative n.1) w)*
      Real.sqrt (cappedRepresentative n.2)*Real.sqrt (J n))≤
      Real.sqrt E*(2*Real.sqrt N+2*(P/w)) := by
  have hN : 0≤N := (Nat.cast_nonneg _).trans hpN
  obtain ⟨h1,h2⟩ := pair_source_ratio_sq_sum hP hw S hS hpN hfN
  constructor
  · exact joint_budget_Cauchy hE hN (div_nonneg hP hw.le) S J _ hJ hbudget h1
  · apply joint_budget_weighted_Cauchy hE hN (div_nonneg hP hw.le) S J
      (fun n=>(sourceRepresentative n.1/min (sourceRepresentative n.1) w)*Real.sqrt (cappedRepresentative n.2)) hJ hbudget
    simpa only [mul_pow,Real.sq_sqrt (cappedRepresentative_pos _).le] using h2

lemma pairCountConstant_pos : 0<pairCountConstant := by
  have h : 0<Real.log 2 := Real.log_pos (by norm_num)
  unfold pairCountConstant
  positivity

lemma exists_small_pair_count {P : ℝ} (hP : 1≤P) (hL : 1≤Real.log (2+P)) :
    ∃N : ℕ, (N:ℝ)≤pairCountConstant*Real.log (2+P) ∧
    ∀np nf : ℕ,sourceRepresentative np≤P →
      1/sourceRepresentative np ≤ cappedRepresentative nf → np<N ∧ nf<N := by
  obtain ⟨N,hN,hcard⟩ := exists_dyadic_count_log hP
  refine ⟨N,?_,?_⟩
  · have h2 : 0<Real.log 2 := Real.log_pos (by norm_num)
    apply hcard.trans
    have hl : Real.log P≤Real.log (2+P) := Real.log_le_log (zero_lt_one.trans_le hP) (by linarith)
    have hd := div_le_div_of_nonneg_right hl h2.le
    unfold pairCountConstant
    simp only [div_eq_mul_inv,one_mul] at hd ⊢
    nlinarith
  · intro np nf hp hf
    have hn : np+6<N := index_lt_of_two_pow_le (by rwa [←sourceRepresentative_two_pow]) hN
    have hnf := selection_angle_index hf
    omega

lemma small_pair_cardinals {P : ℝ} (hP : 1≤P) (hL : 1≤Real.log (2+P))
    (S : Finset (ℕ×ℕ)) (hS : ∀n∈S,sourceRepresentative n.1≤P ∧
      1/sourceRepresentative n.1 ≤ cappedRepresentative n.2) :
    ((S.image Prod.fst).card:ℝ)≤pairCountConstant*Real.log (2+P) ∧
    ((S.image Prod.snd).card:ℝ)≤pairCountConstant*Real.log (2+P) := by
  obtain ⟨N,hN,hidx⟩ := exists_small_pair_count hP hL
  have hp : S.image Prod.fst⊆Finset.range N := by
    intro n hn
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_range.mpr (hidx k.1 k.2 (hS k hk).1 (hS k hk).2).1
  have hf : S.image Prod.snd⊆Finset.range N := by
    intro n hn
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_range.mpr (hidx k.1 k.2 (hS k hk).1 (hS k hk).2).2
  constructor
  · have hc : ((S.image Prod.fst).card:ℝ)≤(N:ℝ) := by exact_mod_cast (Finset.card_le_card hp).trans_eq (Finset.card_range N)
    exact hc.trans hN
  · have hc : ((S.image Prod.snd).card:ℝ)≤(N:ℝ) := by exact_mod_cast (Finset.card_le_card hf).trans_eq (Finset.card_range N)
    exact hc.trans hN

lemma angle_sqrt_factor {A L φ : ℝ} (hA : 0≤A) (hL : 0≤L) (hφ : 0<φ) :
    φ*Real.sqrt (A*L/φ)=Real.sqrt (A*L)*Real.sqrt φ := by
  calc
    _=Real.sqrt (φ^2)*Real.sqrt (A*L/φ) := by rw [Real.sqrt_sq hφ.le]
    _=Real.sqrt (A*L*φ) := by
      rw [←Real.sqrt_mul (sq_nonneg φ)]
      congr 1
      field_simp
    _=_ := Real.sqrt_mul (mul_nonneg hA hL) φ

lemma shared_radius_expansion {P M A I p w φ J : ℝ}
    (hP : 0<P) (hM : 0≤M) (hA : 0≤A) (hI : 0≤I)
    (hp : 0<p) (hw : 0<w) (hφ : 0<φ) :
    Real.sqrt I*(1+Real.sqrt (I/stabilityLength P 16384 M A p w φ)*Real.sqrt J)*p*φ=
      Real.sqrt I*p*φ+16384*I*P*(M*(p/min p w)*Real.sqrt J+
        Real.sqrt (A*Real.log (2+P))*(p/min p w)*Real.sqrt φ*Real.sqrt J) := by
  have hL : 0≤Real.log (2+P) := Real.log_nonneg (by linarith)
  have hm : min p w≠0 := (lt_min hp hw).ne'
  have hf := angle_sqrt_factor hA hL hφ
  rw [sqrt_div_stabilityLength hP.le (by norm_num) hM hp.le hw.le hφ.le hI]
  unfold stabilityRate
  calc
    _=Real.sqrt I*p*φ+16384*(Real.sqrt I)^2*P*
        (M*(p/min p w)+(φ*Real.sqrt (A*Real.log (2+P)/φ))*(p/min p w))*Real.sqrt J := by
      field_simp
    _=_ := by rw [Real.sq_sqrt hI,hf]; ring

lemma source_receiver_pair_sum {P : ℝ} (hP : 0≤P) (S : Finset (ℕ×ℕ))
    (hS : ∀n∈S,sourceRepresentative n.1≤P) :
    ∑n∈S,sourceRepresentative n.1*cappedRepresentative n.2≤4*P := by
  classical
  let U := S.image Prod.fst
  let V := S.image Prod.snd
  have hU (n) (hn : n∈U) : sourceRepresentative n≤P := by
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hn
    exact hS k hk
  have hsub : S⊆U.product V := by
    intro n hn
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨n,hn,rfl⟩,Finset.mem_image.mpr ⟨n,hn,rfl⟩⟩
  have hv : ∑n∈V,cappedRepresentative n≤2 := by
    have hh := capped_positive_power_sum_unscaled (by norm_num : (0:ℝ)<1)
      (by norm_num : (0:ℝ)<1) V (fun n _=>cappedRepresentative_le_one n)
    norm_num at hh
    exact hh
  calc
    _≤∑n∈U.product V,sourceRepresentative n.1*cappedRepresentative n.2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _=>by
        have hp : 0 < sourceRepresentative n.1 := by dsimp [sourceRepresentative]; positivity
        exact mul_nonneg hp.le (cappedRepresentative_pos _).le)
    _=(∑n∈U,sourceRepresentative n)*(∑n∈V,cappedRepresentative n) := by
      rw [Finset.product_eq_sprod,Finset.sum_product,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.mul_sum]
    _≤(2*P)*2 := mul_le_mul (sourceRepresentative_sum_bound hP U hU) hv
      (Finset.sum_nonneg (fun n _=>(cappedRepresentative_pos _).le)) (by positivity)
    _=_ := by ring

lemma paired_count_Cauchy_factors {C L X : ℝ} (hC : 0≤C) (hL : 1≤L) (hX : 1≤X) :
    C*L+2*Real.sqrt (C*L)*X≤(C+2*Real.sqrt C)*L*X ∧
    2*Real.sqrt (C*L)+2*X≤(2*Real.sqrt C+2)*Real.sqrt L*X := by
  have hL0 : 0≤L := zero_le_one.trans hL
  have hX0 : 0≤X := zero_le_one.trans hX
  have hroot : 1≤Real.sqrt L := by simpa using Real.sqrt_le_sqrt hL
  have hrL : Real.sqrt L≤L := by nlinarith [Real.sq_sqrt hL0]
  rw [Real.sqrt_mul hC]
  constructor
  · have h1 : C*L≤C*L*X := le_mul_of_one_le_right (mul_nonneg hC hL0) hX
    have h2 : 2*(Real.sqrt C*Real.sqrt L)*X≤2*(Real.sqrt C*L)*X := by gcongr
    nlinarith
  · have h1 : 2*(Real.sqrt C*Real.sqrt L)≤2*(Real.sqrt C*Real.sqrt L)*X :=
      le_mul_of_one_le_right (by positivity) hX
    have h2 : 2*X≤2*Real.sqrt L*X := by nlinarith
    nlinarith

lemma shared_radius_pair_sum {P M A I w E : ℝ}
    (hP : 1≤P) (hL : 1≤Real.log (2+P)) (hM : 0≤M) (hA : 0≤A)
    (hI : 0≤I) (hw : 0<w) (hwP : w≤P) (hE : 0≤E)
    (S : Finset (ℕ×ℕ)) (J : ℕ×ℕ→ℝ) (hJ : ∀n∈S,0≤J n)
    (hbudget : ∑n∈S,J n≤E) (hS : ∀n∈S,sourceRepresentative n.1≤P ∧
      1/sourceRepresentative n.1 ≤ cappedRepresentative n.2) :
    let D := pairCountConstant+4*Real.sqrt pairCountConstant+2
    (∑n∈S, Real.sqrt I*(1+Real.sqrt (I/stabilityLength P 16384 M A
      (sourceRepresentative n.1) w (cappedRepresentative n.2))*Real.sqrt (J n))*
      sourceRepresentative n.1*cappedRepresentative n.2)≤
      (4+16384*Real.sqrt E*D)*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w) := by
  dsimp only
  let L := Real.log (2+P)
  let C := pairCountConstant
  let D := C+4*Real.sqrt C+2
  have hP0 : 0<P := zero_lt_one.trans_le hP
  have hL0 : 0≤L := zero_le_one.trans hL
  have hC : 0≤C := pairCountConstant_pos.le
  have hD : 0≤D := by dsimp [D]; positivity
  have hS' : ∀n∈S,sourceRepresentative n.1≤P := fun n hn=>(hS n hn).1
  obtain ⟨hc1,hc2⟩ := small_pair_cardinals hP hL S hS
  obtain ⟨hb1,hb2⟩ := shared_weighted_pair_Cauchy hP0.le hw hE S J hJ hbudget hS' hc1 hc2
  obtain ⟨hf1,hf2⟩ := paired_count_Cauchy_factors hC hL ((one_le_div hw).mpr hwP)
  have hD1 : C+2*Real.sqrt C≤D := by dsimp [D]; linarith [Real.sqrt_nonneg C]
  have hD2 : 2*Real.sqrt C+2≤D := by dsimp [D]; linarith [Real.sqrt_nonneg C]
  have hu : (∑n∈S,(sourceRepresentative n.1/min (sourceRepresentative n.1) w)*Real.sqrt (J n))≤
      Real.sqrt E*(D*L*(P/w)) := by
    apply hb1.trans
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg E)
    exact hf1.trans (by gcongr)
  have hv : (∑n∈S,(sourceRepresentative n.1/min (sourceRepresentative n.1) w)*Real.sqrt (cappedRepresentative n.2)*Real.sqrt (J n))≤
      Real.sqrt E*(D*Real.sqrt L*(P/w)) := by
    apply hb2.trans
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg E)
    exact hf2.trans (by gcongr)
  have hsum := source_receiver_pair_sum hP0.le S hS'
  have hex (n : ℕ×ℕ) (hn : n∈S) := shared_radius_expansion (J:=J n) hP0 hM hA hI
    (show 0 < sourceRepresentative n.1 by dsimp [sourceRepresentative]; positivity) hw (cappedRepresentative_pos n.2)
  calc
    _=Real.sqrt I*(∑n∈S,sourceRepresentative n.1*cappedRepresentative n.2)+
        16384*I*P*(M*(∑n∈S,(sourceRepresentative n.1/min (sourceRepresentative n.1) w)*Real.sqrt (J n))+
        Real.sqrt (A*L)*(∑n∈S,(sourceRepresentative n.1/min (sourceRepresentative n.1) w)*Real.sqrt (cappedRepresentative n.2)*Real.sqrt (J n))) := by
      rw [Finset.sum_congr rfl hex]
      rw [Finset.sum_add_distrib]
      congr 1
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n hn
        ring
      · rw [←Finset.mul_sum]
        congr 1
        rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro n hn
        dsimp [L]
        ring
    _≤Real.sqrt I*(4*P)+16384*I*P*(M*(Real.sqrt E*(D*L*(P/w)))+
        Real.sqrt (A*L)*(Real.sqrt E*(D*Real.sqrt L*(P/w)))) := by gcongr
    _=4*(P*Real.sqrt I)+(16384*Real.sqrt E*D)*((M+Real.sqrt A)*I*P^2*L/w) := by
      rw [Real.sqrt_mul hA]
      have hr : (Real.sqrt L)^2=L := Real.sq_sqrt hL0
      simp only [div_eq_mul_inv]
      ring_nf
      rw [hr]
      ring
    _≤_ := by
      have hx : 0≤P*Real.sqrt I := by positivity
      have hy : 0≤(M+Real.sqrt A)*I*P^2*L/w := by positivity
      nlinarith [mul_nonneg (show 0≤16384*Real.sqrt E*D by positivity) hx]

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_SharedOccupation
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

lemma representativeJointEnergy_nonneg {T : ℝ} (s : Solution) (F : PhaseFlowOn s.E s.B T)
    (zX : Phase) (a b I : ℝ) (n : ℕ×ℕ) :
    0 ≤ representativeJointEnergy s F zX a b I n := ENNReal.toReal_nonneg

lemma representativeSharedRadius_one_le {T : ℝ} (s : Solution) (F : PhaseFlowOn s.E s.B T)
    (zX : Phase) (P M A w a b I : ℝ) (n : ℕ×ℕ) :
    1 ≤ representativeSharedRadius s F zX P M A w a b I n := by
  unfold representativeSharedRadius
  exact le_add_of_nonneg_right (by positivity)

lemma central_shared_radial_sum {I R p θ φ : ℝ}
    (hI : 0<I) (hR : 0<R) (hp : 0<p) (hθ : 0<θ) (hφ : 0<φ) :
    (∑'n : ℕ,ENNReal.ofReal (min (I*cappedRepresentative n*p^3*θ^2*φ^2)
      (R^2/(p*cappedRepresentative n*φ^2))))≤
      ENNReal.ofReal (6*Real.sqrt I*R*p*θ) := by
  let g : ℤ→ℝ := fun k=>min (I*p^3*θ*φ^4*((2:ℝ)^k)) (R^2/(p*θ*((2:ℝ)^k)))
  have hg0 (k : ℤ) : 0≤g k := by dsimp [g]; positivity
  have hg := geometry_radial_balance hI hR hp hθ hφ (by norm_num : (0:ℝ)<1)
  simp only [one_mul] at hg
  have he (n : ℕ) : cappedRepresentative n=(2:ℝ)^(-(n:ℤ)) := by
    simp only [cappedRepresentative,zpow_neg,zpow_natCast,inv_pow]
  have hinj : Function.Injective (fun n : ℕ=>-(n:ℤ)) := by
    intro a b hab
    exact_mod_cast neg_injective hab
  have hscale (h : ℝ) (hh : 0<h) :
      min (I*h*p^3*θ^2*φ^2) (R^2/(p*h*φ^2))=
      (θ/φ^2)*min (I*p^3*θ*φ^4*h) (R^2/(p*θ*h)) := by
    rw [mul_min_of_nonneg _ _ (by positivity : 0≤θ/φ^2)]
    congr 1 <;> field_simp
  simp_rw [hscale _ (cappedRepresentative_pos _),ENNReal.ofReal_mul (by positivity : 0≤θ/φ^2),he]
  rw [ENNReal.tsum_mul_left]
  calc
    _≤ENNReal.ofReal (θ/φ^2)*(∑'k : ℤ,ENNReal.ofReal (g k)) :=
      mul_le_mul' le_rfl (ENNReal.tsum_comp_le_tsum_of_injective hinj (fun k=>ENNReal.ofReal (g k)))
    _=ENNReal.ofReal (θ/φ^2)*ENNReal.ofReal (∑'k : ℤ,g k) := by
      rw [ENNReal.ofReal_tsum_of_nonneg hg0 hg.1]
    _≤ENNReal.ofReal (θ/φ^2)*ENNReal.ofReal (6*Real.sqrt I*R*p*φ^2) :=
      mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hg.2)
    _=ENNReal.ofReal (6*Real.sqrt I*R*p*θ) := by
      rw [←ENNReal.ofReal_mul (by positivity : 0≤θ/φ^2)]
      congr 1
      field_simp

lemma capped_linear_tail_sum {φ : ℝ} (hφ : 0<φ) :
    (∑'n : ℕ,ENNReal.ofReal (if cappedRepresentative n≤φ then cappedRepresentative n else 0))≤
      ENNReal.ofReal (2*φ) := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro S
  let U := S.filter (fun n=>cappedRepresentative n≤φ)
  have he : (∑n∈S,ENNReal.ofReal (if cappedRepresentative n≤φ then cappedRepresentative n else 0))=
      ∑n∈U,ENNReal.ofReal (cappedRepresentative n) := by simp [U,Finset.sum_filter,apply_ite]
  rw [he,←ENNReal.ofReal_sum_of_nonneg (fun n _=>(cappedRepresentative_pos n).le)]
  apply ENNReal.ofReal_le_ofReal
  have hh := capped_positive_power_sum_unscaled hφ (by norm_num : (0:ℝ)<1) U
    (fun n hn=>(Finset.mem_filter.mp hn).2)
  norm_num only [Real.rpow_one] at hh
  exact hh

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_CentralOccupation
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

lemma Admissible.representative_regular_central_double_sum {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M A P : ℝ,0<M → 0≤A → 0<P →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (np nf : ℕ) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → 0<I → b-a≤I → 0<w →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let p := sourceRepresentative np
      let φ := cappedRepresentative nf
      let R := representativeSharedRadius s F zX P M A w a b I (np,nf)
      (∑'nt : ℕ,∑'nr : ℕ,if cappedRepresentative nt≤φ/16 then
        representativeRegularCentralCost s F zX P M A I w ![np,nt,nf,nr] a b else 0)≤
        ENNReal.ofReal (C*Real.sqrt I*R*p*φ) := by
  classical
  obtain ⟨C,hC,hbound⟩ := hd.representative_regular_central_shared T₀
  refine ⟨12*C,by positivity,?_⟩
  intro M A P hM hA hP s T F hs hT hTT zX np nf a b I w hzX ha hb hI hJI hw HZ
  dsimp only
  let p := sourceRepresentative np
  let φ := cappedRepresentative nf
  let R := representativeSharedRadius s F zX P M A w a b I (np,nf)
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  have hφ : 0<φ := cappedRepresentative_pos _
  have hR : 0<R := zero_lt_one.trans_le (representativeSharedRadius_one_le _ _ _ _ _ _ _ _ _ _ _)
  have hr (nt : ℕ) (hnt : cappedRepresentative nt≤φ/16) :
      (∑'nr : ℕ,representativeRegularCentralCost s F zX P M A I w ![np,nt,nf,nr] a b)≤
      ENNReal.ofReal (C*(6*Real.sqrt I*R*p*cappedRepresentative nt)) := by
    calc
      _≤∑'nr : ℕ,ENNReal.ofReal (C*min
          (I*cappedRepresentative nr*p^3*(cappedRepresentative nt)^2*φ^2)
          (R^2/(p*cappedRepresentative nr*φ^2))) := by
        apply ENNReal.tsum_le_tsum
        intro nr
        exact hbound M A P hM hA hP s T F hs hT hTT zX ![np,nt,nf,nr] a b I w
          hzX ha hb hI hJI hw hnt HZ
      _=ENNReal.ofReal C*(∑'nr : ℕ,ENNReal.ofReal (min
          (I*cappedRepresentative nr*p^3*(cappedRepresentative nt)^2*φ^2)
          (R^2/(p*cappedRepresentative nr*φ^2)))) := by
        simp_rw [ENNReal.ofReal_mul hC,ENNReal.tsum_mul_left]
      _≤ENNReal.ofReal C*ENNReal.ofReal (6*Real.sqrt I*R*p*cappedRepresentative nt) :=
        mul_le_mul' le_rfl (central_shared_radial_sum hI hR hp (cappedRepresentative_pos _) hφ)
      _=_ := (ENNReal.ofReal_mul hC).symm
  have hsum : (∑'nt : ℕ,∑'nr : ℕ,if cappedRepresentative nt≤φ/16 then
      representativeRegularCentralCost s F zX P M A I w ![np,nt,nf,nr] a b else 0)≤
      ENNReal.ofReal (6*C*Real.sqrt I*R*p)*
        (∑'nt : ℕ,ENNReal.ofReal (if cappedRepresentative nt≤φ then cappedRepresentative nt else 0)) := by
    rw [←ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro nt
    by_cases ht : cappedRepresentative nt≤φ/16
    · have ht' : cappedRepresentative nt≤φ := ht.trans (by linarith)
      simp only [ite_eq_left ht,ite_eq_left ht']
      apply (hr nt ht).trans_eq
      rw [←ENNReal.ofReal_mul (by positivity : 0≤6*C*Real.sqrt I*R*p)]
      congr 1
      ring
    · simp only [ite_eq_right ht,tsum_zero]
      exact bot_le
  apply hsum.trans
  calc
    _≤ENNReal.ofReal (6*C*Real.sqrt I*R*p)*ENNReal.ofReal (2*φ) :=
      mul_le_mul' le_rfl (capped_linear_tail_sum hφ)
    _=_ := by rw [←ENNReal.ofReal_mul (by positivity : 0≤6*C*Real.sqrt I*R*p)]; congr 1; ring

lemma Admissible.central_regular_uniform_oai {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M A P : ℝ,0<M → 0≤A → 1≤P → 1≤Real.log (2+P) →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → 0<I → b-a≤I → 0<w → w≤P →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let Q := {n : ℕ×ℕ | sourceRepresentative n.1≤P ∧
        1/sourceRepresentative n.1 ≤ cappedRepresentative n.2}
      (∑'n : ℕ×ℕ,Q.indicator (fun n=>∑'nt : ℕ,∑'nr : ℕ,
        if cappedRepresentative nt ≤ cappedRepresentative n.2/16 then
          representativeRegularCentralCost s F zX P M A I w ![n.1,nt,n.2,nr] a b else 0) n)≤
        ENNReal.ofReal (C*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w)) := by
  classical
  obtain ⟨Cc,hCc,hcentral⟩ := hd.representative_regular_central_double_sum T₀
  let E := 3468*datumEnergyNumber d
  let D := pairCountConstant+4*Real.sqrt pairCountConstant+2
  let K := 4+16384*Real.sqrt E*D
  have hE : 0≤E := mul_nonneg (by norm_num) hd.datumEnergyNumber_nonneg
  have hD : 0≤D := by dsimp [D]; exact add_nonneg (add_nonneg pairCountConstant_pos.le (by positivity)) (by norm_num)
  have hK : 0≤K := by dsimp [K]; positivity
  refine ⟨Cc*K,mul_nonneg hCc hK,?_⟩
  intro M A P hM hA hP hL s T F hs hT hTT zX a b I w hzX ha hb hI hJI hw hwP HZ
  dsimp only
  let Q := {n : ℕ×ℕ | sourceRepresentative n.1≤P ∧
    1/sourceRepresentative n.1 ≤ cappedRepresentative n.2}
  let J := representativeJointEnergy s F zX a b I
  let R := representativeSharedRadius s F zX P M A w a b I
  have hP0 : 0<P := zero_lt_one.trans_le hP
  have hR (n : ℕ×ℕ) : 0<R n := zero_lt_one.trans_le (representativeSharedRadius_one_le ..)
  have hp (n : ℕ) : 0 < sourceRepresentative n := by dsimp [sourceRepresentative]; positivity
  have hpair (n : ℕ×ℕ) (hn : n∈Q) : sourceRepresentative n.1≤P ∧
      1/sourceRepresentative n.1 ≤ cappedRepresentative n.2 := hn
  obtain ⟨hJs,hJsum,hJeq⟩ := hs.representativeJointEnergy_sum hd F zX hI hJI
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro S
  let U := S.filter (fun n=>n∈Q)
  have hU (n) (hn : n∈U) : n∈Q := (Finset.mem_filter.mp hn).2
  have he : (∑n∈S,Q.indicator (fun n=>∑'nt : ℕ,∑'nr : ℕ,
      if cappedRepresentative nt ≤ cappedRepresentative n.2/16 then
        representativeRegularCentralCost s F zX P M A I w ![n.1,nt,n.2,nr] a b else 0) n)=
      ∑n∈U,(∑'nt : ℕ,∑'nr : ℕ,if cappedRepresentative nt ≤ cappedRepresentative n.2/16 then
        representativeRegularCentralCost s F zX P M A I w ![n.1,nt,n.2,nr] a b else 0) := by
    simp [U,Finset.sum_filter,indicator_apply]
  rw [he]
  have hJn (n : ℕ×ℕ) : 0≤J n := representativeJointEnergy_nonneg ..
  have hbudget : ∑n∈U,J n≤E := (hJs.sum_le_tsum U (fun n _=>hJn n)).trans hJsum
  have hn := shared_radius_pair_sum hP hL hM.le hA hI.le hw hwP hE U J
    (fun n _=>hJn n) hbudget (fun n hn=>hpair n (hU n hn))
  change (∑n∈U,Real.sqrt I*R n*sourceRepresentative n.1*cappedRepresentative n.2)≤
    K*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w) at hn
  calc
    _≤∑n∈U,ENNReal.ofReal (Cc*Real.sqrt I*R n*sourceRepresentative n.1*cappedRepresentative n.2) := by
      apply Finset.sum_le_sum
      intro n hn
      exact hcentral M A P hM hA hP0 s T F hs hT hTT zX n.1 n.2 a b I w
        hzX ha hb hI hJI hw HZ
    _=ENNReal.ofReal (Cc*(∑n∈U,Real.sqrt I*R n*sourceRepresentative n.1*cappedRepresentative n.2)) := by
      rw [←ENNReal.ofReal_sum_of_nonneg (fun n _=>by
        exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCc (Real.sqrt_nonneg I)) (hR n).le) (hp _).le) (cappedRepresentative_pos _).le)]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _≤_ := ENNReal.ofReal_le_ofReal (by
      have hh := mul_le_mul_of_nonneg_left hn hCc
      simpa only [mul_assoc] using hh)

end RVM

end

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

end

end OAI
end

theorem solution : type_of% @OAI.RVM.Admissible.central_regular_uniform_oai := @OAI.RVM.Admissible.central_regular_uniform_oai
