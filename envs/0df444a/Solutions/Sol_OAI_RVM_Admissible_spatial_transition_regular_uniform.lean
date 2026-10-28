-- Prove2me | solution 1 for OAI.RVM.Admissible.spatial_transition_regular_uniform
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:29:32.077192+00:00
-- url     : https://prove2.me/submissions/41455c1d-3349-4a11-93f7-97f02150a2db

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000
import Theorems.Thm_OAI_RVM_Admissible_representative_regular_central_shared
import Theorems.Thm_OAI_RVM_Admissible_unselected_spatial_polynomial_cap
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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_RepresentativeCosts
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

lemma sourceRepresentative_le_four {a b : ℕ} (h : a ≤ b+2) :
    sourceRepresentative a ≤ 4*sourceRepresentative b := by
  have hp := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) h
  dsimp only [sourceRepresentative]
  calc
    64*(2:ℝ)^a ≤ 64*(2:ℝ)^(b+2) := mul_le_mul_of_nonneg_left hp (by norm_num)
    _ = _ := by rw [pow_add]; ring

lemma cappedRepresentative_le_four {a b : ℕ} (h : b ≤ a+2) :
    cappedRepresentative a ≤ 4*cappedRepresentative b := by
  have hp := pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ 2⁻¹) (by norm_num : (2:ℝ)⁻¹ ≤ 1) h
  dsimp only [cappedRepresentative]
  rw [pow_add] at hp
  norm_num at hp
  nlinarith

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

lemma crossing_normalisation {n D α : ℝ} (hn : 0<n) (hD : 0<D)
    (_hα : 0<α) :
    n^(1/(α+1))*(D^2/n)^(α/(α+1)) = D*(n/D)^((1-α)/(1+α)) := by
  rw [Real.div_rpow (sq_nonneg D) hn.le,←Real.rpow_natCast_mul hD.le]
  rw [Real.div_rpow hn.le hD.le]
  norm_num only [Nat.cast_ofNat]
  have he : 1/(α+1)-α/(α+1)=(1-α)/(1+α) := by ring
  have hnexp : n^(1/(α+1))/n^(α/(α+1))=n^((1-α)/(1+α)) := by
    rw [←Real.rpow_sub hn,he]
  rw [show n^(1/(α+1))*(D^((2:ℝ)*(α/(α+1)))/n^(α/(α+1)))=
    (n^(1/(α+1))/n^(α/(α+1)))*D^((2:ℝ)*(α/(α+1))) by ring,hnexp]
  have he' : (2:ℝ)*(α/(α+1))=1-(1-α)/(1+α) := by field_simp; ring
  rw [he',Real.rpow_sub hD,Real.rpow_one]
  ring

lemma angular_crossing_sum {x γ q : ℝ} (hx : 0<x) (hγ : 0<γ) (hq : 0<q) :
    Summable (fun k : ℤ=>min ((x*((2:ℝ)^k)^γ)^q) ((x*((2:ℝ)^k)^γ)^(-1:ℝ))) ∧
    (∑' k : ℤ,min ((x*((2:ℝ)^k)^γ)^q) ((x*((2:ℝ)^k)^γ)^(-1:ℝ))) ≤
      dyadicBalanceConstant (γ*q) γ := by
  have hgq : 0<γ*q := mul_pos hγ hq
  have he (k : ℤ) : min ((x*((2:ℝ)^k)^γ)^q) ((x*((2:ℝ)^k)^γ)^(-1:ℝ))=
      min (x^q*((2:ℝ)^k)^(γ*q)) (x^(-1:ℝ)*((2:ℝ)^k)^(-γ)) := by
    rw [Real.mul_rpow hx.le (Real.rpow_nonneg (zpow_pos (by norm_num : (0:ℝ)<2) k).le γ),
      Real.mul_rpow hx.le (Real.rpow_nonneg (zpow_pos (by norm_num : (0:ℝ)<2) k).le γ),
      ←Real.rpow_mul (zpow_pos (by norm_num : (0:ℝ)<2) k).le,
      ←Real.rpow_mul (zpow_pos (by norm_num : (0:ℝ)<2) k).le]
    simp only [mul_neg_one]
  simp_rw [he]
  refine ⟨dyadic_power_min_summable (Real.rpow_pos_of_pos hx _).le
    (Real.rpow_pos_of_pos hx _).le hgq hγ,?_⟩
  have hh := dyadic_balance (Real.rpow_pos_of_pos hx q) (Real.rpow_pos_of_pos hx (-1)) hgq hγ
  have heq : (x^q)^(γ/(γ*q+γ))*(x^(-1:ℝ))^((γ*q)/(γ*q+γ))=1 := by
    rw [←Real.rpow_mul hx.le,←Real.rpow_mul hx.le,←Real.rpow_add hx]
    rw [show q*(γ/(γ*q+γ))+(-1)*((γ*q)/(γ*q+γ))=0 by ring,Real.rpow_zero]
  simpa only [heq,mul_one,dyadicBalanceConstant] using hh

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

namespace RVM

lemma small_power_four {x y e : ℝ} (hx : 0≤x) (hy : 0≤y)
    (he : 0≤e) (he1 : e≤1) (hxy : x≤4*y) : x^e≤4*y^e := by
  calc
    x^e≤(4*y)^e := Real.rpow_le_rpow hx hxy he
    _=(4:ℝ)^e*y^e := Real.mul_rpow (by norm_num) hy
    _≤4*y^e := mul_le_mul_of_nonneg_right (by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤4) he1)
      (Real.rpow_nonneg hy _)

lemma small_negative_power_four {x y e : ℝ} (hx : 0<x) (hy : 0<y)
    (he : 0≤e) (he1 : e≤1) (hyx : y≤4*x) : x^(-e)≤4*y^(-e) := by
  have hinv : x⁻¹≤4*y⁻¹ := by
    rw [inv_eq_one_div,←div_eq_mul_inv]
    exact (div_le_div_iff₀ hx hy).mpr (by simpa using hyx)
  simpa only [Real.rpow_neg_eq_inv_rpow] using small_power_four (inv_nonneg.mpr hx.le)
    (inv_nonneg.mpr hy.le) he he1 hinv

lemma selectionWeight_neighbor {P : ℝ} (hP : 0<P) {j k : Fin 4→ℕ}
    (hjk : ∀i,j i≤k i+2 ∧ k i≤j i+2) :
    selectionWeight P (cappedRepresentative (k 1)) (cappedRepresentative (k 2))
      (cappedRepresentative (k 3))≤64*
    selectionWeight P (cappedRepresentative (j 1)) (cappedRepresentative (j 2))
      (cappedRepresentative (j 3)) := by
  have hc (n : ℕ) : 0 < cappedRepresentative n := cappedRepresentative_pos _
  have hθ := small_negative_power_four (mul_pos hP (hc (k 1))) (mul_pos hP (hc (j 1)))
    (by norm_num : (0:ℝ)≤1/100000) (by norm_num : (1:ℝ)/100000≤1)
    (show P*cappedRepresentative (j 1)≤4*(P*cappedRepresentative (k 1)) from by
      have hh := mul_le_mul_of_nonneg_left (cappedRepresentative_le_four (hjk 1).2) hP.le
      simpa only [mul_left_comm] using hh)
  have hφ := small_power_four (hc (k 2)).le (hc (j 2)).le
    (by norm_num : (0:ℝ)≤1/100000) (by norm_num : (1:ℝ)/100000≤1)
    (cappedRepresentative_le_four (hjk 2).1)
  have hh := small_power_four (hc (k 3)).le (hc (j 3)).le
    (by norm_num : (0:ℝ)≤1/100000) (by norm_num : (1:ℝ)/100000≤1)
    (cappedRepresentative_le_four (hjk 3).1)
  have hjθ := hc (j 1)
  have hjφ := hc (j 2)
  have hjh := hc (j 3)
  have hkθ := hc (k 1)
  have hkφ := hc (k 2)
  have hkh := hc (k 3)
  unfold selectionWeight
  simp only [neg_div]
  calc
    _≤(4*(P*cappedRepresentative (j 1))^(-(1/100000:ℝ)))*
        (4*(cappedRepresentative (j 2))^(1/100000:ℝ))*
        (4*(cappedRepresentative (j 3))^(1/100000:ℝ)) := by
      apply mul_le_mul (mul_le_mul hθ hφ (by positivity) (by positivity)) hh (by positivity) (by positivity)
    _=_ := by ring

lemma selected_neighbor_near_lower {P M A w I : ℝ} (hP : 0<P) (hI : 0<I)
    {j k : Fin 4→ℕ} (hj : representativeSelected P M A w I j)
    (hjk : ∀i,j i≤k i+2 ∧ k i≤j i+2) :
    P*Real.sqrt I*selectionWeight P (cappedRepresentative (k 1))
        (cappedRepresentative (k 2)) (cappedRepresentative (k 3)) <
      32768*(I*Real.sqrt (cappedRepresentative (k 3))*(sourceRepresentative (k 0))^2*
        (cappedRepresentative (k 2))^2) := by
  have hp (n : ℕ) : 0 < sourceRepresentative n := by dsimp [sourceRepresentative]; positivity
  have hc (n : ℕ) : 0 < cappedRepresentative n := cappedRepresentative_pos _
  have hnear := lt_of_lt_of_le hj (min_le_left _ _)
  have hsqrt : Real.sqrt (cappedRepresentative (j 3))≤2*Real.sqrt (cappedRepresentative (k 3)) := by
    calc
      _≤Real.sqrt (4*cappedRepresentative (k 3)) := Real.sqrt_le_sqrt (cappedRepresentative_le_four (hjk 3).2)
      _=_ := by rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤4)]; norm_num
  have hcost : I*Real.sqrt (cappedRepresentative (j 3))*(sourceRepresentative (j 0))^2*
      (cappedRepresentative (j 2))^2≤512*(I*Real.sqrt (cappedRepresentative (k 3))*
        (sourceRepresentative (k 0))^2*(cappedRepresentative (k 2))^2) := by
    calc
      _≤I*(2*Real.sqrt (cappedRepresentative (k 3)))*(4*sourceRepresentative (k 0))^2*
          (4*cappedRepresentative (k 2))^2 := by
        apply mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hsqrt hI.le)
          (pow_le_pow_left₀ (hp _).le (sourceRepresentative_le_four (hjk 0).1) 2) (by positivity) (by positivity))
          (pow_le_pow_left₀ (hc _).le (cappedRepresentative_le_four (hjk 2).2) 2) (by positivity) (by positivity)
      _=_ := by ring
  calc
    _≤64*(P*Real.sqrt I*selectionWeight P (cappedRepresentative (j 1))
        (cappedRepresentative (j 2)) (cappedRepresentative (j 3))) := by
      have hh := mul_le_mul_of_nonneg_left (selectionWeight_neighbor hP hjk)
        (mul_nonneg hP.le (Real.sqrt_nonneg I))
      simpa only [mul_left_comm] using hh
    _<64*(I*Real.sqrt (cappedRepresentative (j 3))*(sourceRepresentative (j 0))^2*
        (cappedRepresentative (j 2))^2) := mul_lt_mul_of_pos_left hnear (by norm_num)
    _≤64*(512*(I*Real.sqrt (cappedRepresentative (k 3))*(sourceRepresentative (k 0))^2*
        (cappedRepresentative (k 2))^2)) := mul_le_mul_of_nonneg_left hcost (by norm_num)
    _=_ := by ring

end RVM

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

lemma Admissible.representative_spatial_regular_shared {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M A P : ℝ,0<M → 0≤A → 0<P →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (k : Fin 4→ℕ) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → 0<I → b-a≤I → 0<w →
      cappedRepresentative (k 1) ≤ cappedRepresentative (k 2)/16 →
      regularCentralIndex P M A I w k →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let p := sourceRepresentative (k 0)
      let θ := cappedRepresentative (k 1)
      let φ := cappedRepresentative (k 2)
      let h := cappedRepresentative (k 3)
      let R := representativeSharedRadius s F zX P M A w a b I (k 0,k 2)
      representativeSpatialCost s F zX w k a b≤
        ENNReal.ofReal (C*min (I*h*p^3*θ*φ^3) (R^2/(p*h*θ*φ))) := by
  obtain ⟨C,hC,hbound⟩ := hd.representative_regular_central_shared T₀
  refine ⟨C,hC,?_⟩
  intro M A P hM hA hP s T F hs hT hTT zX k a b I w hzX ha hb hI hJI hw hsmall hreg HZ
  dsimp only
  have hθ := cappedRepresentative_pos (k 1)
  have hφ := cappedRepresentative_pos (k 2)
  have hbnd := hbound M A P hM hA hP s T F hs hT hTT zX k a b I w hzX ha hb hI hJI hw hsmall HZ
  dsimp only at hbnd
  rw [representativeRegularCentralCost,ite_eq_left hreg] at hbnd
  apply (mul_le_mul' le_rfl hbnd).trans
  rw [←ENNReal.ofReal_mul (by positivity : 0 ≤ cappedRepresentative (k 2)/cappedRepresentative (k 1))]
  apply le_of_eq
  congr 1
  rw [show cappedRepresentative (k 2)/cappedRepresentative (k 1)*
    (C*min _ _) = C*((cappedRepresentative (k 2)/cappedRepresentative (k 1))*min _ _) by ring,
    mul_min_of_nonneg _ _ (by positivity : 0 ≤ cappedRepresentative (k 2)/cappedRepresentative (k 1))]
  congr 2 <;> field_simp

end RVM

end

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_GoodCrossings
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

lemma capped_negative_power_sum {x α : ℝ} (hx : 0<x) (hα : 0<α)
    (S : Finset ℕ) (hS : ∀j∈S,x ≤ cappedRepresentative j) :
    ∑j∈S,(x/cappedRepresentative j)^α≤(1-((2:ℝ)⁻¹)^α)⁻¹ := by
  classical
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
      exact (hS j₀ hj₀).trans_eq (by rw [he,mul_comm])
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
      _≤∑j∈S,(((2:ℝ)⁻¹)^α)^(j₀-j) := Finset.sum_le_sum hpoint
      _=∑m∈S.image (fun j=>j₀-j),(((2:ℝ)⁻¹)^α)^m := (Finset.sum_image hinj).symm
      _≤∑'m : ℕ,(((2:ℝ)⁻¹)^α)^m :=
        (summable_geometric_of_norm_lt_one hnorm).sum_le_tsum _ (fun _ _=>by positivity)
      _=_ := tsum_geometric_of_norm_lt_one hnorm
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.sum_empty]
    exact inv_nonneg.mpr (sub_nonneg.mpr hbase1.le)

lemma capped_inverse_head_sum {x : ℝ} (hx : 0<x) :
    (∑'j : ℕ,if x ≤ cappedRepresentative j then ENNReal.ofReal (x/cappedRepresentative j) else 0)≤2 := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro S
  let U := S.filter (fun j=>x ≤ cappedRepresentative j)
  have he : (∑j∈S,if x ≤ cappedRepresentative j then ENNReal.ofReal (x/cappedRepresentative j) else 0)=
      ∑j∈U,ENNReal.ofReal (x/cappedRepresentative j) := by simp [U,Finset.sum_filter]
  rw [he,←ENNReal.ofReal_sum_of_nonneg (fun j _=>div_nonneg hx.le (cappedRepresentative_pos j).le)]
  have hb := capped_negative_power_sum hx (by norm_num : (0:ℝ)<1) U
    (fun j hj=>(Finset.mem_filter.mp hj).2)
  norm_num at hb
  exact (ENNReal.ofReal_le_ofReal hb).trans_eq (by norm_num)

lemma capped_balance_sum {a b α β : ℝ} (ha : 0<a) (hb : 0<b)
    (hα : 0<α) (hβ : 0<β) :
    (∑'j : ℕ,ENNReal.ofReal (min (a*(cappedRepresentative j)^α)
      (b*(cappedRepresentative j)^(-β))))≤
      ENNReal.ofReal (dyadicBalanceConstant α β*(a^(β/(α+β))*b^(α/(α+β)))) := by
  let g : ℤ→ℝ := fun k=>min (a*((2:ℝ)^k)^α) (b*((2:ℝ)^k)^(-β))
  have hg : Summable g := dyadic_power_min_summable ha.le hb.le hα hβ
  have hg0 (k : ℤ) : 0≤g k := by dsimp [g]; positivity
  have he (j : ℕ) : cappedRepresentative j=(2:ℝ)^(-(j:ℤ)) := by
    simp only [cappedRepresentative,zpow_neg,zpow_natCast,inv_pow]
  have hi : Function.Injective (fun j : ℕ=>-(j:ℤ)) := by
    intro a b hab
    exact_mod_cast neg_injective hab
  simp_rw [he]
  calc
    _≤∑'k : ℤ,ENNReal.ofReal (g k) := ENNReal.tsum_comp_le_tsum_of_injective hi _
    _=ENNReal.ofReal (∑'k : ℤ,g k) := (ENNReal.ofReal_tsum_of_nonneg hg0 hg).symm
    _≤_ := ENNReal.ofReal_le_ofReal (dyadic_balance ha hb hα hβ)

lemma scaled_capped_crossing_sum {n f x α : ℝ} (hn : 0<n) (hf : 0<f)
    (hx : 0<x) (hα : 0<α) :
    (∑'j : ℕ,if x ≤ cappedRepresentative j then
      ENNReal.ofReal (min (n*(cappedRepresentative j/x)^α)
        (f*(cappedRepresentative j/x)^(-1:ℝ))) else 0)≤
      ENNReal.ofReal (min (2*f)
        (dyadicBalanceConstant α 1*(n^(1/(α+1))*f^(α/(α+1))))) := by
  classical
  rw [ENNReal.ofReal_min]
  apply le_min
  · calc
      _≤∑'j : ℕ,if x ≤ cappedRepresentative j then
          ENNReal.ofReal f*ENNReal.ofReal (x/cappedRepresentative j) else 0 := by
        apply ENNReal.tsum_le_tsum
        intro j
        split_ifs
        · rw [←ENNReal.ofReal_mul hf.le,Real.rpow_neg_one,inv_div]
          exact ENNReal.ofReal_le_ofReal (min_le_right _ _)
        · rfl
      _=ENNReal.ofReal f*(∑'j : ℕ,if x ≤ cappedRepresentative j then
          ENNReal.ofReal (x/cappedRepresentative j) else 0) := by
        rw [←ENNReal.tsum_mul_left]
        apply tsum_congr
        intro j
        split_ifs <;> simp
      _≤ENNReal.ofReal f*2 := mul_le_mul' le_rfl (capped_inverse_head_sum hx)
      _=ENNReal.ofReal (2*f) := by rw [mul_comm,ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2)]; norm_num
  · have hnorm : (n/x^α)^(1/(α+1))*(f*x)^(α/(α+1))=
        n^(1/(α+1))*f^(α/(α+1)) := by
      rw [Real.div_rpow hn.le (Real.rpow_nonneg hx.le _),Real.mul_rpow hf.le hx.le,
        ←Real.rpow_mul hx.le]
      have he : α*(1/(α+1))=α/(α+1) := by ring
      rw [he]
      have hz := (Real.rpow_pos_of_pos hx (α/(α+1))).ne'
      field_simp
    have he (j : ℕ) : min (n*(cappedRepresentative j/x)^α)
        (f*(cappedRepresentative j/x)^(-1:ℝ))=
        min ((n/x^α)*(cappedRepresentative j)^α) ((f*x)*(cappedRepresentative j)^(-1:ℝ)) := by
      rw [Real.div_rpow (cappedRepresentative_pos j).le hx.le,Real.rpow_neg_one,
        Real.rpow_neg_one,inv_div]
      congr 1 <;> ring
    calc
      _≤∑'j : ℕ,ENNReal.ofReal (min ((n/x^α)*(cappedRepresentative j)^α)
          ((f*x)*(cappedRepresentative j)^(-1:ℝ))) := by
        apply ENNReal.tsum_le_tsum
        intro j
        split_ifs
        · exact le_of_eq (congrArg ENNReal.ofReal (he j))
        · exact bot_le
      _≤ENNReal.ofReal (dyadicBalanceConstant α 1*
          ((n/x^α)^(1/(α+1))*(f*x)^(α/(α+1)))) :=
        capped_balance_sum (div_pos hn (Real.rpow_pos_of_pos hx _)) (mul_pos hf hx) hα (by norm_num)
      _=_ := by rw [hnorm]

lemma crossing_bound_normalised {n D α : ℝ} (hn : 0<n) (hD : 0<D)
    (hα : 0<α) :
    min (2*(D^2/n))
      (dyadicBalanceConstant α 1*(n^(1/(α+1))*(D^2/n)^(α/(α+1))))≤
      (2+dyadicBalanceConstant α 1)*D*
        min ((n/D)^((1-α)/(1+α))) ((n/D)^(-1:ℝ)) := by
  have hC := dyadicBalanceConstant_pos hα (by norm_num : (0:ℝ)<1)
  have he : D^2/n=D*(n/D)^(-1:ℝ) := by rw [Real.rpow_neg_one,inv_div]; ring
  rw [crossing_normalisation hn hD hα,
    mul_min_of_nonneg _ _ (by positivity : 0≤(2+dyadicBalanceConstant α 1)*D)]
  apply le_min
  · apply (min_le_right _ _).trans
    have hn0 : 0≤D*(n/D)^((1-α)/(1+α)) := by positivity
    nlinarith only [mul_nonneg (by norm_num : (0:ℝ)≤2) hn0]
  · apply (min_le_left _ _).trans
    rw [he]
    have hn0 : 0≤D*(n/D)^(-1:ℝ) := by positivity
    nlinarith only [mul_nonneg hC.le hn0]

lemma scaled_capped_crossing_normalised {n D x α : ℝ} (hn : 0<n) (hD : 0<D)
    (hx : 0<x) (hα : 0<α) :
    (∑'j : ℕ,if x ≤ cappedRepresentative j then
      ENNReal.ofReal (min (n*(cappedRepresentative j/x)^α)
        ((D^2/n)*(cappedRepresentative j/x)^(-1:ℝ))) else 0)≤
      ENNReal.ofReal ((2+dyadicBalanceConstant α 1)*D*
        min ((n/D)^((1-α)/(1+α))) ((n/D)^(-1:ℝ))) :=
  (scaled_capped_crossing_sum hn (div_pos (sq_pos_of_pos hD) hn) hx hα).trans
    (ENNReal.ofReal_le_ofReal (crossing_bound_normalised hn hD hα))

lemma scaled_two_level_crossing_sum {N D α γ : ℝ} (hN : 0<N) (hD : 0<D)
    (hα : 0<α) (hα1 : α<1) (hγ : 0<γ) (x : ℕ→ℝ) (hx : ∀j,0<x j) :
    (∑'nt : ℕ,∑'nr : ℕ,if x nt ≤ cappedRepresentative nr then
      ENNReal.ofReal (min ((N*(cappedRepresentative nt)^γ)*(cappedRepresentative nr/x nt)^α)
        ((D^2/(N*(cappedRepresentative nt)^γ))*(cappedRepresentative nr/x nt)^(-1:ℝ)))
      else 0)≤
      ENNReal.ofReal ((2+dyadicBalanceConstant α 1)*D*
        dyadicBalanceConstant (γ*((1-α)/(1+α))) γ) := by
  let q : ℝ := (1-α)/(1+α)
  let K : ℝ := (2+dyadicBalanceConstant α 1)*D
  have hq : 0<q := div_pos (sub_pos.mpr hα1) (by linarith)
  have hK : 0≤K := by dsimp [K]; positivity [dyadicBalanceConstant_pos hα (by norm_num : (0:ℝ)<1)]
  let g : ℤ→ℝ := fun k=>min (((N/D)*((2:ℝ)^k)^γ)^q) (((N/D)*((2:ℝ)^k)^γ)^(-1:ℝ))
  have hg := angular_crossing_sum (div_pos hN hD) hγ hq
  have hg0 (k : ℤ) : 0≤g k := by dsimp [g]; positivity
  have he (j : ℕ) : cappedRepresentative j=(2:ℝ)^(-(j:ℤ)) := by
    simp only [cappedRepresentative,zpow_neg,zpow_natCast,inv_pow]
  have hi : Function.Injective (fun j : ℕ=>-(j:ℤ)) := by
    intro a b hab
    exact_mod_cast neg_injective hab
  calc
    _≤∑'nt : ℕ,ENNReal.ofReal K*ENNReal.ofReal (g (-(nt:ℤ))) := by
      apply ENNReal.tsum_le_tsum
      intro nt
      have hb := scaled_capped_crossing_normalised
        (mul_pos hN (Real.rpow_pos_of_pos (cappedRepresentative_pos nt) γ)) hD (hx nt) hα
      apply hb.trans_eq
      rw [←ENNReal.ofReal_mul hK]
      congr 1
      dsimp [K,g,q]
      rw [he]
      congr 2 <;> congr 1 <;> ring
    _=ENNReal.ofReal K*(∑'nt : ℕ,ENNReal.ofReal (g (-(nt:ℤ)))) := ENNReal.tsum_mul_left
    _≤ENNReal.ofReal K*(∑'k : ℤ,ENNReal.ofReal (g k)) :=
      mul_le_mul' le_rfl (ENNReal.tsum_comp_le_tsum_of_injective hi (fun index => ENNReal.ofReal (g index)))
    _=ENNReal.ofReal K*ENNReal.ofReal (∑'k : ℤ,g k) := by
      rw [ENNReal.ofReal_tsum_of_nonneg hg0 hg.1]
    _≤ENNReal.ofReal K*ENNReal.ofReal (dyadicBalanceConstant (γ*q) γ) :=
      mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hg.2)
    _=_ := by rw [←ENNReal.ofReal_mul hK]

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma spatial_crossing_scale {b α θ : ℝ} (hb : 0<b) (hα : α<1) (hθ : 0<θ) :
    (b^(1/(1-α))*θ^(-α/(1-α)))^(1-α)=b*θ^(-α) := by
  rw [Real.mul_rpow (Real.rpow_pos_of_pos hb _).le (Real.rpow_pos_of_pos hθ _).le,
    ←Real.rpow_mul hb.le,←Real.rpow_mul hθ.le]
  have hne : (1-α)≠0 := by linarith
  rw [show (1/(1-α))*(1-α)=1 by field_simp,
    show (-α/(1-α))*(1-α) = -α by field_simp,Real.rpow_one]

lemma spatial_crossing_normalisation {a b c α θ h : ℝ}
    (ha : 0<a) (hb : 0<b) (hc : 0 < c) (hα : α<1) (hθ : 0<θ) (hh : 0<h) :
    let H := b^(1/(1-α))
    let x := H*θ^(-α/(1-α))
    let N := a*H/b
    let γ := (1-2*α)/(1-α)
    let D := Real.sqrt (a*c/b)
    (N*θ^γ)*(h/x)^α=a*θ^(1-α)*h^α ∧
    (D^2/(N*θ^γ))*(h/x)^(-1:ℝ)=c/(θ*h) := by
  dsimp only
  let H := b^(1/(1-α))
  let δ := -α/(1-α)
  let x := H*θ^δ
  let γ := (1-2*α)/(1-α)
  have hH : 0<H := Real.rpow_pos_of_pos hb _
  have hx : 0<x := mul_pos hH (Real.rpow_pos_of_pos hθ _)
  have hne : (1-α)≠0 := by linarith
  have hγ : γ=1+δ := by dsimp [γ,δ]; field_simp; ring
  have hn : (a*H/b)*θ^γ=(a/b)*θ*x := by
    rw [hγ,Real.rpow_add hθ,Real.rpow_one]
    dsimp [x]
    ring
  have hs : x^(1-α)=b*θ^(-α) := spatial_crossing_scale hb hα hθ
  have hxa : x=x^α*(b*θ^(-α)) := by
    rw [←hs,←Real.rpow_add hx,show α+(1-α)=1 by ring,Real.rpow_one]
  have hθa : θ*θ^(-α)=θ^(1-α) := by
    calc
      _=θ^(1:ℝ)*θ^(-α) := by rw [Real.rpow_one]
      _=θ^(1-α) := by rw [←Real.rpow_add hθ]; congr 1
  change ((a*H/b)*θ^γ)*(h/x)^α=_ ∧ _
  rw [hn]
  constructor
  · rw [Real.div_rpow hh.le hx.le]
    calc
      _=(a/b)*θ*(x^α*(b*θ^(-α)))*(h^α/x^α) := by rw [←hxa]
      _=a*(θ*θ^(-α))*h^α := by field_simp
      _=_ := by rw [hθa]
  · rw [Real.sq_sqrt (by positivity : 0≤a*c/b),Real.rpow_neg_one]
    change ((a*c/b)/((a/b)*θ*x))*(h/x)⁻¹=c/(θ*h)
    field_simp

lemma spatial_transition_double_sum {a b c α : ℝ}
    (ha : 0<a) (hb : 0<b) (hc : 0 < c) (hα : 0<α) (hα2 : α<1/2) :
    let γ := (1-2*α)/(1-α)
    (∑'nt : ℕ,∑'nr : ℕ,
      if b*(cappedRepresentative nt)^(-α)≤(cappedRepresentative nr)^(1-α) then
        ENNReal.ofReal (min (a*(cappedRepresentative nt)^(1-α)*(cappedRepresentative nr)^α)
          (c/(cappedRepresentative nt*cappedRepresentative nr))) else 0)≤
      ENNReal.ofReal ((2+dyadicBalanceConstant α 1)*Real.sqrt (a*c/b)*
        dyadicBalanceConstant (γ*((1-α)/(1+α))) γ) := by
  dsimp only
  have hα1 : α<1 := by linarith
  have hβ : 0<1-α := by linarith
  let H := b^(1/(1-α))
  let x := fun nt=>H*(cappedRepresentative nt)^(-α/(1-α))
  let N := a*H/b
  let D := Real.sqrt (a*c/b)
  let γ := (1-2*α)/(1-α)
  have hH : 0<H := Real.rpow_pos_of_pos hb _
  have hx (j : ℕ) : 0<x j := mul_pos hH (Real.rpow_pos_of_pos (cappedRepresentative_pos j) _)
  have hN : 0<N := div_pos (mul_pos ha hH) hb
  have hD : 0<D := Real.sqrt_pos.mpr (by positivity)
  have hγ : 0<γ := div_pos (by linarith) hβ
  have hbound := scaled_two_level_crossing_sum hN hD hα hα1 hγ x hx
  apply le_of_eq_of_le _ hbound
  apply tsum_congr
  intro nt
  apply tsum_congr
  intro nr
  have hs := spatial_crossing_scale hb hα1 (cappedRepresentative_pos nt)
  change (x nt)^(1-α)=b*(cappedRepresentative nt)^(-α) at hs
  have he : (b*(cappedRepresentative nt)^(-α)≤(cappedRepresentative nr)^(1-α)) ↔
      x nt ≤ cappedRepresentative nr := by
    rw [←hs,Real.rpow_le_rpow_iff (hx nt).le (cappedRepresentative_pos nr).le hβ]
  simp only [he]
  split_ifs
  · have hn := spatial_crossing_normalisation ha hb hc hα1
      (cappedRepresentative_pos nt) (cappedRepresentative_pos nr)
    rw [hn.1,hn.2]
  · rfl

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_ReceiverWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RVM

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff


lemma selectionWeight_pos {P θ φ h : ℝ} (hP : 0<P) (hθ : 0<θ) (hφ : 0<φ) (hh : 0<h) :
    0 < selectionWeight P θ φ h := by unfold selectionWeight; positivity

lemma selectionWeight_sq {P θ φ h : ℝ} (hP : 0<P) (hθ : 0<θ) (hφ : 0<φ) (hh : 0<h) :
    selectionWeight P θ φ h ^ 2 =
      P^(-(1/50000:ℝ))*θ^(-(1/50000:ℝ))*φ^(1/50000:ℝ)*h^(1/50000:ℝ) := by
  have he {x e : ℝ} (hx : 0<x) : (x^e)^2=x^(e*2) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hx.le]
    norm_num
  unfold selectionWeight
  rw [mul_pow,mul_pow,he (mul_pos hP hθ),he hφ,he hh,
    Real.mul_rpow hP.le hθ.le]
  norm_num

lemma spatialThresholdA_pos {P p φ : ℝ} (hP : 0<P) (hp : 0<p) (hφ : 0<φ) :
    0 < spatialThresholdA P p φ := by unfold spatialThresholdA; positivity

lemma spatialThresholdB_pos {P I p φ : ℝ} (hP : 0<P) (hI : 0<I) (hp : 0<p) (hφ : 0<φ) :
    0 < spatialThresholdB P I p φ := by unfold spatialThresholdB; positivity

lemma spatial_polynomial_normalisation {P p θ φ h : ℝ}
    (hP : 0<P) (hp : 0<p) (hθ : 0<θ) (hφ : 0<φ) (hh : 0<h) :
    P^2*(selectionWeight P θ φ h)^2*θ/(p*φ)=
      spatialThresholdA P p φ*θ^(1-(1/50000:ℝ))*h^(1/50000:ℝ) := by
  rw [selectionWeight_sq hP hθ hφ hh]
  have he : θ^(-(1/50000:ℝ))*θ=θ^(1-(1/50000:ℝ)) := by
    rw [mul_comm]
    calc
      _=θ^(1:ℝ)*θ^(-(1/50000:ℝ)) := by rw [Real.rpow_one]
      _=_ := by rw [←Real.rpow_add hθ]; norm_num
  unfold spatialThresholdA
  calc
    _=(P^2*P^(-(1/50000:ℝ))*φ^(1/50000:ℝ)/(p*φ))*
       (θ^(-(1/50000:ℝ))*θ)*h^(1/50000:ℝ) := by
         apply (div_eq_iff (mul_pos hp hφ).ne').mpr
         field_simp
    _=_ := by rw [he]

lemma near_lower_radial_condition {P I p θ φ h : ℝ}
    (hP : 0<P) (hI : 0<I) (hp : 0<p) (hθ : 0<θ) (hφ : 0<φ) (hh : 0<h)
    (hnear : P*Real.sqrt I*selectionWeight P θ φ h <
      32768*(I*Real.sqrt h*p^2*φ^2)) :
    spatialThresholdB P I p φ*θ^(-(1/50000:ℝ))≤h^(1-(1/50000:ℝ)) := by
  have hWpos := selectionWeight_pos hP hθ hφ hh
  have hs := pow_le_pow_left₀ (by positivity : 0≤P*Real.sqrt I*selectionWeight P θ φ h) hnear.le 2
  have hW := selectionWeight_sq hP hθ hφ hh
  have hr : h^(1-(1/50000:ℝ))*h^(1/50000:ℝ)=h := by
    rw [←Real.rpow_add hh]
    norm_num
  let B := (32768:ℝ)^2*(I:ℝ)^2*p^4*φ^4*h^(1/50000:ℝ)
  have hB : 0<B := by dsimp [B]; positivity
  apply (mul_le_mul_iff_right₀ hB).mp
  calc
    _=(P*Real.sqrt I*selectionWeight P θ φ h)^2 := by
      rw [mul_pow,mul_pow,Real.sq_sqrt hI.le,hW]
      dsimp [spatialThresholdB,B]
      field_simp
    _≤(32768*(I*Real.sqrt h*p^2*φ^2))^2 := hs
    _=B*h^(1-(1/50000:ℝ)) := by
      rw [mul_pow,mul_pow,mul_pow,mul_pow,Real.sq_sqrt hh.le]
      dsimp [B]
      calc
        _=(32768:ℝ)^2*(I:ℝ)^2*p^4*φ^4*h := by ring
        _=(32768:ℝ)^2*(I:ℝ)^2*p^4*φ^4*(h^(1-(1/50000:ℝ))*h^(1/50000:ℝ)) := by rw [hr]
        _=_ := by ring

lemma selected_neighbor_radial_condition {P M A w I : ℝ} (hP : 0<P) (hI : 0<I)
    {j k : Fin 4→ℕ} (hj : representativeSelected P M A w I j)
    (hjk : ∀i,j i≤k i+2 ∧ k i≤j i+2) :
    spatialThresholdB P I (sourceRepresentative (k 0)) (cappedRepresentative (k 2))*
      (cappedRepresentative (k 1))^(-(1/50000:ℝ))≤
        (cappedRepresentative (k 3))^(1-(1/50000:ℝ)) := by
  exact near_lower_radial_condition hP hI (by dsimp [sourceRepresentative]; positivity)
    (cappedRepresentative_pos _) (cappedRepresentative_pos _) (cappedRepresentative_pos _)
    (selected_neighbor_near_lower hP hI hj hjk)

lemma spatial_crossing_datum_scale {P I p φ R : ℝ}
    (hP : 0<P) (hI : 0<I) (hp : 0<p) (hφ : 0<φ) (hR : 0≤R) :
    Real.sqrt (spatialThresholdA P p φ*(R^2/(p*φ))/spatialThresholdB P I p φ)=
      32768*Real.sqrt I*R*p*φ := by
  have he : spatialThresholdA P p φ*(R^2/(p*φ))/spatialThresholdB P I p φ=
      (32768*R*p*φ)^2*I := by
    unfold spatialThresholdA spatialThresholdB
    field_simp
  rw [he,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (by positivity)]
  ring

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff



open Set Filter Metric MeasureTheory _root_.Classical
open scoped ENNReal Topology ContDiff


end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_SpatialEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RVM

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff



section
open Set Filter Metric MeasureTheory _root_.Classical
open scoped ENNReal Topology ContDiff


lemma Admissible.regular_spatial_transition_pair_sum {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M A : ℝ,0<M → 0<A → ∀ᶠ P : ℝ in atTop,
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (np nf : ℕ) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → a≤b → 0<I → b-a≤I → 0<w →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      (∑'nt : ℕ,∑'nr : ℕ,if cappedRepresentative nt ≤ cappedRepresentative nf/16 ∧
          regularCentralIndex P M A I w ![np,nt,nf,nr] ∧
          representativeSpatialTransition P M A w I ![np,nt,nf,nr] then
        representativeSpatialCost s F zX w ![np,nt,nf,nr] a b else 0)≤
      ENNReal.ofReal (C*Real.sqrt I*
        representativeSharedRadius s F zX P M A w a b I (np,nf)*
        sourceRepresentative np*cappedRepresentative nf) := by
  classical
  obtain ⟨Cu,hCu,hunselected⟩ := hd.unselected_spatial_polynomial_cap T₀
  obtain ⟨Cr,hCr,hregular⟩ := hd.representative_spatial_regular_shared T₀
  let C₀ := max Cu Cr
  have hC₀ : 0≤C₀ := hCu.trans (le_max_left _ _)
  let α : ℝ := 1/50000
  let γ : ℝ := (1-2*α)/(1-α)
  let K := (2+dyadicBalanceConstant α 1)*dyadicBalanceConstant (γ*((1-α)/(1+α))) γ
  have hα : 0<α := by norm_num [α]
  have hα2 : α<1/2 := by norm_num [α]
  have hγ : 0<γ := by norm_num [γ,α]
  have hK : 0<K := mul_pos (by positivity [dyadicBalanceConstant_pos hα (by norm_num : (0:ℝ)<1)])
    (dyadicBalanceConstant_pos (mul_pos hγ (div_pos (by norm_num [α]) (by norm_num [α]))) hγ)
  refine ⟨32768*C₀*K,by positivity,?_⟩
  intro M A hM hA
  filter_upwards [hunselected M A hM hA,eventually_gt_atTop (0:ℝ)] with P hun hP
  intro s T F hs hT hTT zX np nf a b I w hzX ha hb hab hI hJI hw hsource HZ
  let p := sourceRepresentative np
  let φ := cappedRepresentative nf
  let R := representativeSharedRadius s F zX P M A w a b I (np,nf)
  let aa := spatialThresholdA P p φ
  let bb := spatialThresholdB P I p φ
  let cc := R^2/(p*φ)
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  have hφ : 0<φ := cappedRepresentative_pos _
  have hR : 0<R := zero_lt_one.trans_le (representativeSharedRadius_one_le _ _ _ _ _ _ _ _ _ _ _)
  have haa : 0<aa := spatialThresholdA_pos hP hp hφ
  have hbb : 0<bb := spatialThresholdB_pos hP hI hp hφ
  have hcc : 0 < cc := by dsimp [cc]; positivity
  have hpoint (nt nr : ℕ) :
      (if cappedRepresentative nt ≤ cappedRepresentative nf/16 ∧
          regularCentralIndex P M A I w ![np,nt,nf,nr] ∧
          representativeSpatialTransition P M A w I ![np,nt,nf,nr] then
        representativeSpatialCost s F zX w ![np,nt,nf,nr] a b else 0)≤
      ENNReal.ofReal C₀*(if bb*(cappedRepresentative nt)^(-α)≤(cappedRepresentative nr)^(1-α) then
        ENNReal.ofReal (min (aa*(cappedRepresentative nt)^(1-α)*(cappedRepresentative nr)^α)
          (cc/(cappedRepresentative nt*cappedRepresentative nr))) else 0) := by
    by_cases hk : cappedRepresentative nt ≤ cappedRepresentative nf/16 ∧
        regularCentralIndex P M A I w ![np,nt,nf,nr] ∧
        representativeSpatialTransition P M A w I ![np,nt,nf,nr]
    · rw [ite_eq_left hk]
      obtain ⟨hj,hreg,htrans⟩ := hk
      obtain ⟨hfail,j,hsel,hneighbor⟩ := htrans
      have hlower := selected_neighbor_radial_condition hP hI hsel hneighbor
      change bb*(cappedRepresentative nt)^(-α)≤(cappedRepresentative nr)^(1-α) at hlower
      rw [ite_eq_left hlower,←ENNReal.ofReal_mul hC₀]
      have hu := hun s T F hs hT hTT zX ![np,nt,nf,nr] a b I w hzX ha hb hab hI hJI hw
        hj hfail hsource HZ
      have hr := hregular M A P hM hA.le hP s T F hs hT hTT zX ![np,nt,nf,nr] a b I w
        hzX ha hb hI hJI hw hj hreg HZ
      dsimp only at hu hr
      change _≤ENNReal.ofReal (Cu*(P^2*(selectionWeight P (cappedRepresentative nt) φ (cappedRepresentative nr))^2*cappedRepresentative nt/(p*φ))) at hu
      change _≤ENNReal.ofReal (Cr*min (I*cappedRepresentative nr*p^3*cappedRepresentative nt*φ^3) (R^2/(p*cappedRepresentative nr*cappedRepresentative nt*φ))) at hr
      have hnt := cappedRepresentative_pos nt
      have hnr := cappedRepresentative_pos nr
      have hu' : representativeSpatialCost s F zX w ![np,nt,nf,nr] a b≤
          ENNReal.ofReal (C₀*(aa*(cappedRepresentative nt)^(1-α)*(cappedRepresentative nr)^α)) := by
        rw [spatial_polynomial_normalisation hP hp (cappedRepresentative_pos nt) hφ (cappedRepresentative_pos nr)] at hu
        exact hu.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
      have hr' : representativeSpatialCost s F zX w ![np,nt,nf,nr] a b≤
          ENNReal.ofReal (C₀*(cc/(cappedRepresentative nt*cappedRepresentative nr))) := by
        apply hr.trans
        apply ENNReal.ofReal_le_ofReal
        calc
          _≤Cr*(R^2/(p*cappedRepresentative nr*cappedRepresentative nt*φ)) :=
            mul_le_mul_of_nonneg_left (min_le_right _ _) hCr
          _≤C₀*(R^2/(p*cappedRepresentative nr*cappedRepresentative nt*φ)) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
          _=C₀*(cc/(cappedRepresentative nt*cappedRepresentative nr)) := by dsimp [cc]; ring
      rw [mul_min_of_nonneg _ _ hC₀,ENNReal.ofReal_min]
      exact le_min hu' hr'
    · rw [ite_eq_right hk]
      exact bot_le
  calc
    _≤∑'nt : ℕ,∑'nr : ℕ,ENNReal.ofReal C₀*
        (if bb*(cappedRepresentative nt)^(-α)≤(cappedRepresentative nr)^(1-α) then
          ENNReal.ofReal (min (aa*(cappedRepresentative nt)^(1-α)*(cappedRepresentative nr)^α)
            (cc/(cappedRepresentative nt*cappedRepresentative nr))) else 0) :=
      ENNReal.tsum_le_tsum (fun nt=>ENNReal.tsum_le_tsum (hpoint nt))
    _=ENNReal.ofReal C₀*(∑'nt : ℕ,∑'nr : ℕ,
        if bb*(cappedRepresentative nt)^(-α)≤(cappedRepresentative nr)^(1-α) then
          ENNReal.ofReal (min (aa*(cappedRepresentative nt)^(1-α)*(cappedRepresentative nr)^α)
            (cc/(cappedRepresentative nt*cappedRepresentative nr))) else 0) := by
      simp only [ENNReal.tsum_mul_left]
    _≤ENNReal.ofReal C₀*ENNReal.ofReal (K*Real.sqrt (aa*cc/bb)) := by
      apply mul_le_mul' le_rfl
      convert spatial_transition_double_sum haa hbb hcc hα hα2 using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
      dsimp only [K,γ]
      ring
    _= _ := by
      rw [←ENNReal.ofReal_mul hC₀]
      have he := spatial_crossing_datum_scale hP hI hp hφ hR.le
      change Real.sqrt (aa*cc/bb)=32768*Real.sqrt I*R*p*φ at he
      rw [he]
      congr 1
      dsimp only [R,p,φ]
      ring

lemma Admissible.spatial_transition_regular_uniform_oai {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M A : ℝ,0<M → 0<A → ∀ᶠ P : ℝ in atTop,
      1≤P → 1≤Real.log (2+P) →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → a≤b → 0<I → b-a≤I → 0<w → w≤P →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let Q := {n : ℕ×ℕ | sourceRepresentative n.1≤P ∧
        1/sourceRepresentative n.1 ≤ cappedRepresentative n.2}
      (∑'n : ℕ×ℕ,Q.indicator (fun n=>∑'nt : ℕ,∑'nr : ℕ,
        if cappedRepresentative nt ≤ cappedRepresentative n.2/16 ∧
          regularCentralIndex P M A I w ![n.1,nt,n.2,nr] ∧
          representativeSpatialTransition P M A w I ![n.1,nt,n.2,nr] then
          representativeSpatialCost s F zX w ![n.1,nt,n.2,nr] a b else 0) n)≤
        ENNReal.ofReal (C*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w)) := by
  classical
  obtain ⟨Cc,hCc,hcentral⟩ := hd.regular_spatial_transition_pair_sum T₀
  let E := 3468*datumEnergyNumber d
  let D := pairCountConstant+4*Real.sqrt pairCountConstant+2
  let K := 4+16384*Real.sqrt E*D
  have hE : 0≤E := mul_nonneg (by norm_num) hd.datumEnergyNumber_nonneg
  have hD : 0≤D := by dsimp [D]; exact add_nonneg (add_nonneg pairCountConstant_pos.le (by positivity)) (by norm_num)
  have hK : 0≤K := by dsimp [K]; positivity
  refine ⟨Cc*K,mul_nonneg hCc hK,?_⟩
  intro M A hM hA
  filter_upwards [hcentral M A hM hA] with P hc
  intro hP hL s T F hs hT hTT zX a b I w hzX ha hb hab hI hJI hw hwP hsource HZ
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
      if cappedRepresentative nt ≤ cappedRepresentative n.2/16 ∧
        regularCentralIndex P M A I w ![n.1,nt,n.2,nr] ∧
        representativeSpatialTransition P M A w I ![n.1,nt,n.2,nr] then
        representativeSpatialCost s F zX w ![n.1,nt,n.2,nr] a b else 0) n)=
      ∑n∈U,(∑'nt : ℕ,∑'nr : ℕ,if cappedRepresentative nt ≤ cappedRepresentative n.2/16 ∧
        regularCentralIndex P M A I w ![n.1,nt,n.2,nr] ∧
        representativeSpatialTransition P M A w I ![n.1,nt,n.2,nr] then
        representativeSpatialCost s F zX w ![n.1,nt,n.2,nr] a b else 0) := by
    simp [U,Finset.sum_filter,indicator_apply]
  rw [he]
  have hJn (n : ℕ×ℕ) : 0≤J n := representativeJointEnergy_nonneg ..
  have hbudget : ∑n∈U,J n≤E := (hJs.sum_le_tsum U (fun n _=>hJn n)).trans hJsum
  have hn := shared_radius_pair_sum hP hL hM.le hA.le hI.le hw hwP hE U J
    (fun n _=>hJn n) hbudget (fun n hn=>hpair n (hU n hn))
  change (∑n∈U,Real.sqrt I*R n*sourceRepresentative n.1*cappedRepresentative n.2)≤
    K*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w) at hn
  calc
    _≤∑n∈U,ENNReal.ofReal (Cc*Real.sqrt I*R n*sourceRepresentative n.1*cappedRepresentative n.2) := by
      apply Finset.sum_le_sum
      intro n hn
      exact hc s T F hs hT hTT zX n.1 n.2 a b I w
        hzX ha hb hab hI hJI hw hsource HZ
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

theorem solution : type_of% @OAI.RVM.Admissible.spatial_transition_regular_uniform_oai := @OAI.RVM.Admissible.spatial_transition_regular_uniform_oai
