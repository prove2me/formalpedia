-- Prove2me | solution 1 for OAI.RVM.Admissible.good_structural_uniform
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:05:18.657521+00:00
-- url     : https://prove2.me/submissions/a97db9fc-23bd-48c0-8c07-3e80169189e0

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000
import Theorems.Thm_OAI_RVM_Admissible_representative_regular_good_structural_double_sum
import Theorems.Thm_OAI_RVM_Admissible_uniform_actual_bin_Cauchy
import Theorems.Thm_OAI_RVM_EnergyPrefix_goodFieldBudget_uniform
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

lemma ennreal_half_ofReal {x : ℝ} (hx : 0≤x) :
    (ENNReal.ofReal x)^(1/2:ℝ)=ENNReal.ofReal (Real.sqrt x) := by
  rw [Real.sqrt_eq_rpow,ENNReal.ofReal_rpow_of_nonneg hx (by norm_num)]

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

lemma majorant_capped_short_sqrt_radius_sum {H R K : ℝ} (hH : 0<H) (hR : 0<R) (hK : 0≤K) :
    (∑'n : ℕ,if H*cappedRepresentative n≤R then
      ENNReal.ofReal (K*Real.sqrt (H*cappedRepresentative n)) else 0) ≤
    ENNReal.ofReal (K*(1-((2:ℝ)⁻¹)^(1/2:ℝ))⁻¹*Real.sqrt R) := by
  apply ENNReal.tsum_le_of_sum_range_le
  intro N
  let S := (Finset.range N).filter (fun n=>H*cappedRepresentative n≤R)
  have hS : ∀n∈S,cappedRepresentative n≤R/H := by
    intro n hn
    exact (le_div_iff₀ hH).mpr (by simpa only [mul_comm] using (Finset.mem_filter.mp hn).2)
  have hh := capped_positive_power_sum_unscaled (div_pos hR hH) (by norm_num : (0:ℝ)<1/2) S hS
  have he (n : ℕ) : Real.sqrt (H*cappedRepresentative n)=
      Real.sqrt H*(cappedRepresentative n)^(1/2:ℝ) := by
    rw [Real.sqrt_mul hH.le,Real.sqrt_eq_rpow (cappedRepresentative n)]
  calc
    _ = ∑n∈S,ENNReal.ofReal (K*Real.sqrt (H*cappedRepresentative n)) := by
      simp only [S,Finset.sum_filter]
    _ = ENNReal.ofReal (K*Real.sqrt H*(∑n∈S,(cappedRepresentative n)^(1/2:ℝ))) := by
      rw [←ENNReal.ofReal_sum_of_nonneg (fun n hn=>mul_nonneg hK (Real.sqrt_nonneg _))]
      simp only [he,←mul_assoc,Finset.mul_sum]
    _ ≤ ENNReal.ofReal (K*Real.sqrt H*((1-((2:ℝ)⁻¹)^(1/2:ℝ))⁻¹*(R/H)^(1/2:ℝ))) := by
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_left hh (mul_nonneg hK (Real.sqrt_nonneg _))
    _ = _ := by
      rw [←Real.sqrt_eq_rpow (R/H),Real.sqrt_div hR.le]
      congr 1
      field_simp [(Real.sqrt_pos.mpr hH).ne']

lemma majorant_shortSqrtConstant_pos : 0<(1-((2:ℝ)⁻¹)^(1/2:ℝ))⁻¹ := by
  apply inv_pos.mpr
  apply sub_pos.mpr
  exact Real.rpow_lt_one (by norm_num) (by norm_num) (by norm_num)

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_DirectionCutoffs
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

lemma sqrt_near_product {a b I E r φ D : ℝ} (ha : 0≤a) (hb : 0≤b)
    (hI : 0≤I) (hE : 0≤E) (hr : 0 ≤ r) (hφ : 0≤φ) (hD : 0≤D) :
    Real.sqrt (a*E)*Real.sqrt (D^2*(b*I*r*φ^2))=
      D*φ*Real.sqrt (a*I)*Real.sqrt (b*E)*Real.sqrt r := by
  rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq hD]
  calc
    _ = D*Real.sqrt ((a*E)*(b*I*r*φ^2)) := by
      rw [Real.sqrt_mul (mul_nonneg ha hE)]
      ring
    _ = D*Real.sqrt ((a*I)*(b*E)*r*φ^2) := by congr 2; ring
    _ = _ := by
      rw [Real.sqrt_mul (by positivity : 0≤(a*I)*(b*E)*r),
        Real.sqrt_sq hφ,Real.sqrt_mul (by positivity : 0≤(a*I)*(b*E)),
        Real.sqrt_mul (mul_nonneg ha hI)]
      ring

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

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

lemma Admissible.representative_good_Cauchy {d : Datum} (hd : Admissible d) :
    ∃ C : ℝ,0≤C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → ∀(zX : Phase) (k : Fin 4→ℕ) (a b I w : ℝ),
      0≤a → b≤T → 0<I → b-a≤I →
      let p := sourceRepresentative (k 0)
      let θ := cappedRepresentative (k 1)
      let φ := cappedRepresentative (k 2)
      let h := cappedRepresentative (k 3)
      let H := max 1 T
      let B := representativeClosedBin T w k
      let O := coneOccupation F.flow zX T s.f
        (closedBinEulerian F.flow zX T B (tsupport d.f₀) a b
          (max 0 (a-B.rmax)) (min T (b-B.rmin)))
      let E := datumEnergyNumber d
      let D := ENNReal.ofReal (128*C*p^3*θ^2)
      representativeGoodCost s F zX w k a b ≤
        ENNReal.ofReal (φ/(p*θ^2))*((ENNReal.ofReal (20*I*E))^(1/2:ℝ)*
          (min (D^2*ENNReal.ofReal (768*I*(H*h)*φ^2))
            (D*(O/ENNReal.ofReal ((H*h)^2*φ^2/8))))^(1/2:ℝ)) := by
  obtain ⟨C,hC,hbound⟩ := hd.uniform_actual_bin_Cauchy
  refine ⟨C,hC,?_⟩
  intro s T F hs hT zX k a b I w ha hb hI hab
  dsimp only
  let p := sourceRepresentative (k 0)
  let θ := cappedRepresentative (k 1)
  let φ := cappedRepresentative (k 2)
  let r := max 1 T*cappedRepresentative (k 3)
  let B := representativeClosedBin T w k
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  have hθ : 0<θ := cappedRepresentative_pos _
  have hφ : 0<φ := cappedRepresentative_pos _
  have hr : 0 < r := mul_pos (zero_lt_one.trans_le (le_max_left _ _)) (cappedRepresentative_pos _)
  have hJ : Icc a b⊆Icc 0 T := Icc_subset_Icc ha hb
  have hBmax : B.rmax=2*r := by dsimp [B,representativeClosedBin,r]; ring
  have hBmin : B.rmin=r/2 := rfl
  have hmeasure : volume (Icc a b)*ENNReal.ofReal (B.rmax-B.rmin)*ENNReal.ofReal (384*φ^2)≤
      ENNReal.ofReal (768*I*r*φ^2) := by
    calc
      _ ≤ ENNReal.ofReal I*ENNReal.ofReal (2*r)*ENNReal.ofReal (384*φ^2) := by
        apply mul_le_mul' (mul_le_mul' _ _) le_rfl
        · rw [Real.volume_Icc]
          exact ENNReal.ofReal_le_ofReal hab
        · apply ENNReal.ofReal_le_ofReal
          rw [hBmax,hBmin]
          linarith only [hr]
      _ = _ := by rw [←ENNReal.ofReal_mul hI.le,←ENNReal.ofReal_mul (by positivity)]; congr 1; ring
  have hgood : ENNReal.ofReal I*goodFieldBudget s X (fun t=>velocity (V t)) 1 a b I (k 2)≤
      ENNReal.ofReal (20*I*datumEnergyNumber d) := by
    have hh := (ENNReal.le_tsum (k 2)).trans
      (hs.energyPrefix.goodFieldBudget_uniform X (fun t=>velocity (V t)) 1 hJ hI hab)
    rw [hs.initial_energy_eq] at hh
    calc
      _ ≤ ENNReal.ofReal I*((4*1+1:ℕ)*ENNReal.ofReal (4*datumEnergyNumber d)) := mul_le_mul' le_rfl hh
      _ = _ := by
        norm_num only [Nat.reduceMul,Nat.reduceAdd,Nat.cast_ofNat]
        rw [←ENNReal.ofReal_ofNat (n:=5),←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤5),
          ←ENNReal.ofReal_mul hI.le]
        congr 1
        ring
  have hangle (D : ℝ) (hD : D∈Icc B.Dmin B.Dmax) : DyadicWindow 1 (k 2) (Real.sqrt (D/2)) :=
    dyadicWindow_one_sqrt (k 2)
      (by simpa only [B,representativeClosedBin,cappedRepresentative,inv_pow] using hD.1)
      (by simpa only [B,representativeClosedBin,cappedRepresentative,inv_pow] using hD.2)
  have hS0 : tsupport (fun z=>s.f (0,z))⊆tsupport d.f₀ := by
    have he : (fun z=>s.f (0,z))=d.f₀ := funext hs.initial_f
    rw [he]
  have hbnd := hbound s T F hs.energyPrefix hT hs.initial_f zX B (tsupport d.f₀)
    a b I p θ φ 1 1 (k 2) hd.2.1 hS0 hJ hI hp hθ.le hφ.le (by norm_num)
    (by change 0 < r/2; positivity) (by change 0<φ^2/2; positivity)
    (by change p/32≤p; linarith) le_rfl le_rfl (by norm_num [B,representativeClosedBin]) hangle
  dsimp only at hbnd
  have hθ1 : θ≤1 := cappedRepresentative_le_one (k 1)
  simp only [min_eq_left hθ1] at hbnd
  have hden : B.rmin^2*B.Dmin=r^2*φ^2/8 := by change (r/2)^2*(φ^2/2)=_; ring
  rw [hden] at hbnd
  unfold representativeGoodCost
  dsimp only
  apply mul_le_mul' le_rfl
  apply hbnd.trans
  apply mul_le_mul' (ENNReal.rpow_le_rpow hgood (by norm_num))
  apply ENNReal.rpow_le_rpow _ (by norm_num)
  exact min_le_min (mul_le_mul' le_rfl hmeasure) le_rfl

lemma direct_good_near_scalar {C I E H h φ p θ : ℝ}
    (hC : 0≤C) (hI : 0≤I) (hE : 0≤E) (hH : 0≤H) (hh : 0≤h) (hφ : 0≤φ)
    (hp : 0<p) (hθ : 0<θ) :
    (φ/(p*θ^2))*(Real.sqrt (20*I*E)*
      Real.sqrt ((128*C*p^3*θ^2)^2*(768*I*(H*h)*φ^2)))=
    (128*C*Real.sqrt 15360*Real.sqrt E*Real.sqrt H)*(I*Real.sqrt h*p^2*φ^2) := by
  rw [sqrt_near_product (by positivity : 0≤20*I) (by norm_num : (0:ℝ)≤768)
    hI hE (mul_nonneg hH hh) hφ (by positivity)]
  rw [show (20:ℝ)*I*I=20*(I:ℝ)^2 from by ring,Real.sqrt_mul (by norm_num : (0:ℝ)≤20),Real.sqrt_sq hI,
    Real.sqrt_mul (by norm_num : (0:ℝ)≤768),Real.sqrt_mul hH]
  have he : Real.sqrt (20:ℝ)*Real.sqrt 768=Real.sqrt 15360 := by
    rw [←Real.sqrt_mul (by norm_num : (0:ℝ)≤20)]
    norm_num
  calc
    _ = (128*C*(Real.sqrt 20*Real.sqrt 768)*Real.sqrt E*Real.sqrt H)*(I*Real.sqrt h*p^2*φ^2) := by
      field_simp
    _ = _ := by rw [he]

lemma direct_good_near_ennreal {C I E H h φ p θ : ℝ}
    (hC : 0≤C) (hI : 0≤I) (hE : 0≤E) (hH : 0≤H) (hh : 0≤h) (hφ : 0≤φ)
    (hp : 0<p) (hθ : 0<θ) :
    ENNReal.ofReal (φ/(p*θ^2))*((ENNReal.ofReal (20*I*E))^(1/2:ℝ)*
      ((ENNReal.ofReal (128*C*p^3*θ^2))^2*ENNReal.ofReal (768*I*(H*h)*φ^2))^(1/2:ℝ))=
    ENNReal.ofReal ((128*C*Real.sqrt 15360*Real.sqrt E*Real.sqrt H)*(I*Real.sqrt h*p^2*φ^2)) := by
  rw [←ENNReal.ofReal_pow (by positivity : 0≤128*C*p^3*θ^2),
    ←ENNReal.ofReal_mul (sq_nonneg _),ennreal_half_ofReal (by positivity),ennreal_half_ofReal (by positivity),
    ←ENNReal.ofReal_mul (Real.sqrt_nonneg _),←ENNReal.ofReal_mul (by positivity),
    direct_good_near_scalar hC hI hE hH hh hφ hp hθ]

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

lemma capped_square_tail_sum {x : ℝ} (hx : 0<x) :
    (∑'n : ℕ,ENNReal.ofReal (if cappedRepresentative n≤x then (cappedRepresentative n)^2 else 0))≤
      ENNReal.ofReal (2*x^2) := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro S
  let U := S.filter (fun n=>cappedRepresentative n≤x)
  have he : (∑n∈S,ENNReal.ofReal (if cappedRepresentative n≤x then (cappedRepresentative n)^2 else 0))=
      ∑n∈U,ENNReal.ofReal ((cappedRepresentative n)^2) := by simp [U,Finset.sum_filter,apply_ite]
  rw [he,←ENNReal.ofReal_sum_of_nonneg (fun n _=>sq_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  have hh := capped_positive_power_sum_unscaled hx (by norm_num : (0:ℝ)<2) U
    (fun n hn=>(Finset.mem_filter.mp hn).2)
  norm_num at hh
  nlinarith [sq_nonneg x]

lemma sourceRepresentative_one_le (n : ℕ) : 1 ≤ sourceRepresentative n := by
  have h : (1:ℝ)≤2^n := one_le_pow₀ (by norm_num)
  dsimp [sourceRepresentative]
  nlinarith only [h]

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

lemma structural_angle_tsum_le {φ B : ℝ} (hφ : 0<φ) (hB : 0≤B)
    (f : ℕ→ℝ≥0∞)
    (hf : ∀n,φ/16384 ≤ cappedRepresentative n → cappedRepresentative n≤φ/16 →
      f n≤ENNReal.ofReal B) :
    (∑'n : ℕ,if φ/16384 ≤ cappedRepresentative n ∧ cappedRepresentative n≤φ/16 then f n else 0)≤
      ENNReal.ofReal (32768*B) := by
  classical
  have hpoint (n : ℕ) :
      (if φ/16384 ≤ cappedRepresentative n ∧ cappedRepresentative n≤φ/16 then f n else 0)≤
      ENNReal.ofReal (16384*B)*(if φ/16384 ≤ cappedRepresentative n then
        ENNReal.ofReal ((φ/16384)/cappedRepresentative n) else 0) := by
    by_cases hn : φ/16384 ≤ cappedRepresentative n ∧ cappedRepresentative n≤φ/16
    · rw [ite_eq_left hn,ite_eq_left hn.1,←ENNReal.ofReal_mul (by positivity : 0≤16384*B)]
      apply (hf n hn.1 hn.2).trans
      apply ENNReal.ofReal_le_ofReal
      have hθ : cappedRepresentative n≤φ := hn.2.trans (by linarith)
      have hh := mul_le_mul_of_nonneg_left ((one_le_div (cappedRepresentative_pos n)).mpr hθ) hB
      calc
        B=B*1 := (mul_one _).symm
        _≤B*(φ/cappedRepresentative n) := hh
        _=_ := by ring
    · rw [ite_eq_right hn]
      exact bot_le
  apply (ENNReal.tsum_le_tsum hpoint).trans
  rw [ENNReal.tsum_mul_left]
  apply (mul_le_mul' le_rfl (capped_inverse_head_sum (by positivity : 0<φ/16384))).trans_eq
  rw [←ENNReal.ofReal_ofNat (n:=2),←ENNReal.ofReal_mul (by positivity : 0≤16384*B)]
  congr 1
  ring

lemma small_pair_source_sum {P : ℝ} (hP : 1≤P) (hL : 1≤Real.log (2+P))
    (S : Finset (ℕ×ℕ)) (hS : ∀n∈S,sourceRepresentative n.1≤P ∧
      1/sourceRepresentative n.1 ≤ cappedRepresentative n.2) :
    (∑n∈S,sourceRepresentative n.1)≤2*pairCountConstant*P*Real.log (2+P) := by
  classical
  let U := S.image Prod.fst
  let V := S.image Prod.snd
  have hU (n) (hn : n∈U) : sourceRepresentative n≤P := by
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hn
    exact (hS k hk).1
  have hsub : S⊆U.product V := by
    intro n hn
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨n,hn,rfl⟩,Finset.mem_image.mpr ⟨n,hn,rfl⟩⟩
  have hc := (small_pair_cardinals hP hL S hS).2
  have hp : 0≤P := zero_le_one.trans hP
  calc
    _≤∑n∈U.product V,sourceRepresentative n.1 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _=>by dsimp [sourceRepresentative]; positivity)
    _=(∑n∈U,sourceRepresentative n)*(V.card:ℝ) := by
      simp only [Finset.product_eq_sprod,Finset.sum_product,Finset.sum_const,nsmul_eq_mul]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _≤(2*P)*(pairCountConstant*Real.log (2+P)) :=
      mul_le_mul (sourceRepresentative_sum_bound hp U hU) hc (Nat.cast_nonneg _) (by positivity)
    _=_ := by ring

lemma small_pair_I_source_sum {P M A I w : ℝ} (hP : 1≤P) (hL : 1≤Real.log (2+P))
    (hM : 1≤M) (hI : 0≤I) (hw : 0<w) (hwP : w≤P)
    (S : Finset (ℕ×ℕ)) (hS : ∀n∈S,sourceRepresentative n.1≤P ∧
      1/sourceRepresentative n.1 ≤ cappedRepresentative n.2) :
    (∑n∈S,I*sourceRepresentative n.1)≤2*pairCountConstant*
      (P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w) := by
  have hpc := pairCountConstant_pos
  have hP0 : 0<P := zero_lt_one.trans_le hP
  have hL0 : 0≤Real.log (2+P) := zero_le_one.trans hL
  have hstep : I*P*Real.log (2+P)≤(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w := by
    have hm : 1≤M+Real.sqrt A := hM.trans (le_add_of_nonneg_right (Real.sqrt_nonneg A))
    have hratio : 1≤P/w := (one_le_div hw).mpr hwP
    have hh := mul_le_mul_of_nonneg_left (one_le_mul_of_one_le_of_one_le hm hratio)
      (by positivity : 0≤I*P*Real.log (2+P))
    calc
      _=(I*P*Real.log (2+P))*1 := (mul_one _).symm
      _≤(I*P*Real.log (2+P))*((M+Real.sqrt A)*(P/w)) := hh
      _=_ := by ring
  rw [←Finset.mul_sum]
  calc
    _≤I*(2*pairCountConstant*P*Real.log (2+P)) := mul_le_mul_of_nonneg_left (small_pair_source_sum hP hL S hS) hI
    _=2*pairCountConstant*(I*P*Real.log (2+P)) := by ring
    _≤2*pairCountConstant*((M+Real.sqrt A)*I*P^2*Real.log (2+P)/w) :=
      mul_le_mul_of_nonneg_left hstep (by positivity : 0≤2*pairCountConstant)
    _≤_ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity)) (by positivity : 0≤2*pairCountConstant)

lemma Admissible.good_regular_structural_uniform {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M A P : ℝ,1≤M → 0≤A → 1≤P → 1≤Real.log (2+P) →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → 0<I → b-a≤I → 0<w → w≤P →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let Q := {n : ℕ×ℕ | sourceRepresentative n.1≤P ∧
        1/sourceRepresentative n.1 ≤ cappedRepresentative n.2}
      (∑'n : ℕ×ℕ,Q.indicator (fun n=>∑'nt : ℕ,∑'nr : ℕ,
        if cappedRepresentative n.2/16384 ≤ cappedRepresentative nt ∧ cappedRepresentative nt ≤ cappedRepresentative n.2/16 then
          representativeRegularGoodCost s F zX P M A I w ![n.1,nt,n.2,nr] a b else 0) n)≤
        ENNReal.ofReal (C*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w)) := by
  classical
  obtain ⟨Cc,hCc,hcentral⟩ := hd.representative_regular_good_structural_double_sum T₀
  let E := 3468*datumEnergyNumber d
  let D := pairCountConstant+4*Real.sqrt pairCountConstant+2
  let K := 4+16384*Real.sqrt E*D
  have hE : 0≤E := mul_nonneg (by norm_num) hd.datumEnergyNumber_nonneg
  have hD : 0≤D := by dsimp [D]; exact add_nonneg (add_nonneg pairCountConstant_pos.le (by positivity)) (by norm_num)
  have hK : 0≤K := by dsimp [K]; positivity
  refine ⟨Cc*(K+2*pairCountConstant),mul_nonneg hCc (add_nonneg hK (mul_nonneg (by norm_num) pairCountConstant_pos.le)),?_⟩
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
      if cappedRepresentative n.2/16384 ≤ cappedRepresentative nt ∧ cappedRepresentative nt ≤ cappedRepresentative n.2/16 then
        representativeRegularGoodCost s F zX P M A I w ![n.1,nt,n.2,nr] a b else 0) n)=
      ∑n∈U,(∑'nt : ℕ,∑'nr : ℕ,if cappedRepresentative n.2/16384 ≤ cappedRepresentative nt ∧ cappedRepresentative nt ≤ cappedRepresentative n.2/16 then
        representativeRegularGoodCost s F zX P M A I w ![n.1,nt,n.2,nr] a b else 0) := by
    simp [U,Finset.sum_filter,indicator_apply]
  rw [he]
  have hJn (n : ℕ×ℕ) : 0≤J n := representativeJointEnergy_nonneg ..
  have hbudget : ∑n∈U,J n≤E := (hJs.sum_le_tsum U (fun n _=>hJn n)).trans hJsum
  have hn := shared_radius_pair_sum hP hL (zero_le_one.trans hM) hA hI.le hw hwP hE U J
    (fun n _=>hJn n) hbudget (fun n hn=>hpair n (hU n hn))
  change (∑n∈U,Real.sqrt I*R n*sourceRepresentative n.1*cappedRepresentative n.2)≤
    K*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w) at hn
  let B := P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w
  have hn2 := small_pair_I_source_sum (A:=A) hP hL hM hI.le hw hwP U
    (fun n hn=>hpair n (hU n hn))
  have hsum : (∑n∈U,(Real.sqrt I*R n*sourceRepresentative n.1*cappedRepresentative n.2+
      I*sourceRepresentative n.1))≤(K+2*pairCountConstant)*B := by
    rw [Finset.sum_add_distrib]
    calc
      _≤K*B+(2*pairCountConstant)*B := add_le_add hn hn2
      _=_ := by ring
  calc
    _≤∑n∈U,ENNReal.ofReal (Cc*(Real.sqrt I*R n*sourceRepresentative n.1*cappedRepresentative n.2+
        I*sourceRepresentative n.1)) := by
      apply Finset.sum_le_sum
      intro n hn
      exact hcentral M A P (zero_lt_one.trans_le hM) hA hP0 s T F hs hT hTT zX n.1 n.2 a b I w
        hzX ha hb hI hJI hw HZ
    _=ENNReal.ofReal (Cc*(∑n∈U,(Real.sqrt I*R n*sourceRepresentative n.1*cappedRepresentative n.2+
        I*sourceRepresentative n.1))) := by
      rw [←ENNReal.ofReal_sum_of_nonneg (fun n _=>by
        exact mul_nonneg hCc (add_nonneg
          (mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg I) (hR n).le) (hp _).le) (cappedRepresentative_pos _).le)
          (mul_nonneg hI.le (hp _).le)))]
      congr 1
      exact (Finset.mul_sum ..).symm
    _≤_ := ENNReal.ofReal_le_ofReal (by
      have hh := mul_le_mul_of_nonneg_left hsum hCc
      simpa only [B, mul_assoc] using hh)

lemma Admissible.representative_good_near {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ → ∀(zX : Phase) (k : Fin 4→ℕ) (a b I w : ℝ),
      0≤a → b≤T → 0<I → b-a≤I →
      representativeGoodCost s F zX w k a b ≤
        ENNReal.ofReal (C*(I*Real.sqrt (cappedRepresentative (k 3))*(sourceRepresentative (k 0))^2*
          (cappedRepresentative (k 2))^2)) := by
  obtain ⟨Cd,hCd,hmag⟩ := hd.representative_good_Cauchy
  let E := datumEnergyNumber d
  have hE : 0≤E := hd.datumEnergyNumber_nonneg
  refine ⟨128*Cd*Real.sqrt 15360*Real.sqrt E*Real.sqrt (max 1 T₀),by positivity,?_⟩
  intro s T F hs hT hTT zX k a b I w ha hb hI hab
  have hm := hmag s T F hs hT zX k a b I w ha hb hI hab
  dsimp only at hm
  have hp : 0 < sourceRepresentative (k 0) := by dsimp [sourceRepresentative]; positivity
  have hθ := cappedRepresentative_pos (k 1)
  have hφ := cappedRepresentative_pos (k 2)
  have hh := cappedRepresentative_pos (k 3)
  have hH : 0 ≤ max 1 T := zero_le_one.trans (le_max_left _ _)
  apply hm.trans
  apply le_trans _ (le_of_eq (direct_good_near_ennreal hCd hI.le hE hH hh.le hφ.le hp hθ)) |>.trans
  · apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (max_le_max le_rfl hTT)) (by positivity)
  · apply mul_le_mul' le_rfl
    apply mul_le_mul' le_rfl
    exact ENNReal.rpow_le_rpow (min_le_left _ _) (by norm_num)

lemma good_low_coefficient {P p w : ℝ} (hP : 1≤P) (hp : 1≤p)
    (hpP : p≤P) (hw : 1≤w) (hwP : w≤P) :
    p^2*(512/min p w)^2≤512^2*P^2/w := by
  have hP0 : 0<P := zero_lt_one.trans_le hP
  have hp0 : 0<p := zero_lt_one.trans_le hp
  have hw0 : 0<w := zero_lt_one.trans_le hw
  have hP2 : P≤P^2 := by nlinarith only [hP,sq_nonneg (P-1)]
  rcases le_total p w with hpw|hwp
  · rw [min_eq_left hpw]
    have he : p^2*(512/p)^2=512^2 := by field_simp
    rw [he]
    apply (le_div_iff₀ hw0).mpr
    exact mul_le_mul_of_nonneg_left (hwP.trans hP2) (by norm_num)
  · rw [min_eq_right hwp]
    have hww : w≤w^2 := by nlinarith only [hw,sq_nonneg (w-1)]
    calc
      _≤P^2*(512/w)^2 := mul_le_mul_of_nonneg_right (sq_le_sq₀ hp0.le hP0.le |>.mpr hpP) (by positivity)
      _=512^2*(P^2/w^2) := by ring
      _≤512^2*(P^2/w) := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left (sq_nonneg _) hw0 hww) (by norm_num)
      _=_ := by ring

lemma Admissible.representative_low_good_structural_triple_sum {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (np : ℕ) (a b I w : ℝ),
      0≤a → b≤T → 0<I → b-a≤I → 0<w →
      (∑'nf : ℕ,∑'nt : ℕ,∑'nr : ℕ,
        if cappedRepresentative nf/16384 ≤ cappedRepresentative nt ∧ cappedRepresentative nt ≤ cappedRepresentative nf/16 then
          representativeLowShortGoodCost s F zX I w ![np,nt,nf,nr] a b else 0)≤
        ENNReal.ofReal (C*I*Real.sqrt I*(sourceRepresentative np)^2*(512/min (sourceRepresentative np) w)^2) := by
  classical
  obtain ⟨Cn,hCn,hnear⟩ := hd.representative_good_near T₀
  let K := (1-((2:ℝ)⁻¹)^(1/2:ℝ))⁻¹
  have hK : 0<K := majorant_shortSqrtConstant_pos
  refine ⟨65536*Cn*K,by positivity,?_⟩
  intro s T F hs hT hTT zX np a b I w ha hb hI hJI hw
  let p := sourceRepresentative np
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  let G := fun nf nt=>∑'nr : ℕ,representativeLowShortGoodCost s F zX I w ![np,nt,nf,nr] a b
  have hr (nf nt : ℕ) : G nf nt≤ENNReal.ofReal
      (Cn*(I*p^2*(cappedRepresentative nf)^2)*K*Real.sqrt I) := by
    have he (nr : ℕ) : representativeLowShortGoodCost s F zX I w ![np,nt,nf,nr] a b≤
        if cappedRepresentative nr≤I then
          ENNReal.ofReal ((Cn*I*p^2*(cappedRepresentative nf)^2)*Real.sqrt (cappedRepresentative nr)) else 0 := by
      unfold representativeLowShortGoodCost
      change (if cappedRepresentative nf≤512/min p w ∧ cappedRepresentative nr≤I then _ else 0)≤_
      by_cases hh : cappedRepresentative nr≤I
      · rw [ite_eq_left hh]
        split_ifs with hl
        · apply (hnear s T F hs hT hTT zX ![np,nt,nf,nr] a b I w ha hb hI hJI).trans_eq
          congr 1
          dsimp only [Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.head_cons]
          dsimp [p]
          ring
        · exact bot_le
      · rw [ite_eq_right hh,ite_eq_right (fun hc=>hh hc.2)]
    apply (ENNReal.tsum_le_tsum he).trans
    have hh := majorant_capped_short_sqrt_radius_sum (by norm_num : (0:ℝ)<1) hI
      (K:=Cn*I*p^2*(cappedRepresentative nf)^2) (by positivity)
    simp only [one_mul] at hh
    apply hh.trans_eq
    congr 1
    dsimp [K]
    ring
  have hf (nf : ℕ) :
      (∑'nt : ℕ,∑'nr : ℕ,if cappedRepresentative nf/16384 ≤ cappedRepresentative nt ∧ cappedRepresentative nt ≤ cappedRepresentative nf/16 then
        representativeLowShortGoodCost s F zX I w ![np,nt,nf,nr] a b else 0)≤
      if cappedRepresentative nf≤512/min p w then
        ENNReal.ofReal (32768*Cn*K*I*Real.sqrt I*p^2*(cappedRepresentative nf)^2) else 0 := by
    by_cases hl : cappedRepresentative nf≤512/min p w
    · rw [ite_eq_left hl]
      have he (nt : ℕ) : (∑'nr : ℕ,if cappedRepresentative nf/16384 ≤ cappedRepresentative nt ∧ cappedRepresentative nt ≤ cappedRepresentative nf/16 then
          representativeLowShortGoodCost s F zX I w ![np,nt,nf,nr] a b else 0)=
          if cappedRepresentative nf/16384 ≤ cappedRepresentative nt ∧ cappedRepresentative nt ≤ cappedRepresentative nf/16 then G nf nt else 0 := by
        split_ifs <;> simp [G]
      simp_rw [he]
      apply (structural_angle_tsum_le (cappedRepresentative_pos nf) (by positivity) (G nf) (fun nt _ _=>hr nf nt)).trans_eq
      congr 1
      ring
    · rw [ite_eq_right hl]
      have hz (nt nr : ℕ) : representativeLowShortGoodCost s F zX I w ![np,nt,nf,nr] a b=0 := by
        change (if cappedRepresentative nf≤512/min p w ∧ cappedRepresentative nr≤I then _ else 0)=0
        exact ite_eq_right (fun hh=>hl hh.1)
      simp only [hz,ite_self,tsum_zero,le_refl]
  apply (ENNReal.tsum_le_tsum hf).trans
  have hC : 0≤32768*Cn*K*I*Real.sqrt I*p^2 := by positivity
  calc
    _=ENNReal.ofReal (32768*Cn*K*I*Real.sqrt I*p^2)*
      (∑'nf : ℕ,ENNReal.ofReal (if cappedRepresentative nf≤512/min p w then (cappedRepresentative nf)^2 else 0)) := by
      rw [←ENNReal.tsum_mul_left]
      apply tsum_congr
      intro nf
      split_ifs <;> simp [←ENNReal.ofReal_mul hC]
    _≤ENNReal.ofReal (32768*Cn*K*I*Real.sqrt I*p^2)*ENNReal.ofReal (2*(512/min p w)^2) :=
      mul_le_mul' le_rfl (capped_square_tail_sum (by positivity))
    _=_ := by rw [←ENNReal.ofReal_mul hC]; congr 1; ring

lemma Admissible.good_low_uniform {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ P : ℝ,1≤P → 1≤Real.log (2+P) →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (a b I w : ℝ),
      0≤a → b≤T → 0<I → I≤1 → b-a≤I → 1≤w → w≤P →
      let Q := {n : ℕ×ℕ | sourceRepresentative n.1≤P ∧
        1/sourceRepresentative n.1 ≤ cappedRepresentative n.2}
      (∑'n : ℕ×ℕ,Q.indicator (fun n=>∑'nt : ℕ,∑'nr : ℕ,
        if cappedRepresentative n.2/16384 ≤ cappedRepresentative nt ∧ cappedRepresentative nt ≤ cappedRepresentative n.2/16 then
          representativeLowShortGoodCost s F zX I w ![n.1,nt,n.2,nr] a b else 0) n)≤
        ENNReal.ofReal (C*(I*P^2*Real.log (2+P)/w)) := by
  classical
  obtain ⟨Cn,hCn,hnear⟩ := hd.representative_low_good_structural_triple_sum T₀
  have hpc := pairCountConstant_pos
  refine ⟨512^2*Cn*pairCountConstant,by positivity,?_⟩
  intro P hP hL s T F hs hT hTT zX a b I w ha hb hI hI1 hJI hw hwP
  dsimp only
  let Q := {n : ℕ×ℕ | sourceRepresentative n.1≤P ∧
    1/sourceRepresentative n.1 ≤ cappedRepresentative n.2}
  let g := fun np=>∑'nf : ℕ,∑'nt : ℕ,∑'nr : ℕ,
    if cappedRepresentative nf/16384 ≤ cappedRepresentative nt ∧ cappedRepresentative nt ≤ cappedRepresentative nf/16 then
      representativeLowShortGoodCost s F zX I w ![np,nt,nf,nr] a b else 0
  let D := 512^2*Cn*I*P^2/w
  have hP0 : 0<P := zero_lt_one.trans_le hP
  have hw0 : 0<w := zero_lt_one.trans_le hw
  have hD : 0≤D := by dsimp [D]; positivity
  have hgb (np : ℕ) (hn : sourceRepresentative np≤P) : g np≤ENNReal.ofReal D := by
    apply (hnear s T F hs hT hTT zX np a b I w ha hb hI hJI hw0).trans
    apply ENNReal.ofReal_le_ofReal
    have hh := mul_le_mul_of_nonneg_left
      (good_low_coefficient hP (sourceRepresentative_one_le _) hn hw hwP)
      (by positivity : 0≤Cn*I*Real.sqrt I)
    have hsqrt : Real.sqrt I≤1 := (Real.sqrt_le_one).mpr hI1
    calc
      _=(Cn*I*Real.sqrt I)*((sourceRepresentative np)^2*(512/min (sourceRepresentative np) w)^2) := by ring
      _≤(Cn*I*Real.sqrt I)*(512^2*P^2/w) := hh
      _≤(Cn*I*1)*(512^2*P^2/w) := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsqrt (by positivity)) (by positivity)
      _=D := by dsimp [D]; ring
  have hdom : (∑'n : ℕ×ℕ,Q.indicator (fun n=>∑'nt : ℕ,∑'nr : ℕ,
      if cappedRepresentative n.2/16384 ≤ cappedRepresentative nt ∧ cappedRepresentative nt ≤ cappedRepresentative n.2/16 then
        representativeLowShortGoodCost s F zX I w ![n.1,nt,n.2,nr] a b else 0) n)≤
        ∑'np : ℕ,if sourceRepresentative np≤P then g np else 0 := by
    rw [ENNReal.tsum_prod']
    apply ENNReal.tsum_le_tsum
    intro np
    split_ifs with hn
    · apply ENNReal.tsum_le_tsum
      intro nf
      exact (indicator_le_self _ _) (np,nf)
    · have hz (nf : ℕ) : (np,nf)∉Q := fun hh=>hn hh.1
      simp only [indicator_of_notMem (hz _),tsum_zero,le_refl]
  apply hdom.trans
  obtain ⟨N,hN,hidx⟩ := exists_small_pair_count hP hL
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro S
  let U := S.filter (fun np=>sourceRepresentative np≤P)
  have hU (np) (hn : np∈U) : sourceRepresentative np≤P := (Finset.mem_filter.mp hn).2
  have hsub : U⊆Finset.range N := by
    intro np hn
    have hpn : 1/sourceRepresentative np ≤ cappedRepresentative 0 := by
      rw [show cappedRepresentative 0=1 by rfl]
      exact (div_le_one (zero_lt_one.trans_le (sourceRepresentative_one_le _))).mpr (sourceRepresentative_one_le _)
    exact Finset.mem_range.mpr (hidx np 0 (hU np hn) hpn).1
  have hcard : (U.card:ℝ)≤pairCountConstant*Real.log (2+P) := by
    have hh : (U.card:ℝ)≤N := by exact_mod_cast (Finset.card_le_card hsub).trans_eq (Finset.card_range N)
    exact hh.trans hN
  have he : (∑np∈S,if sourceRepresentative np≤P then g np else 0)=∑np∈U,g np := by
    simp [U,Finset.sum_filter]
  rw [he]
  calc
    _≤∑np∈U,ENNReal.ofReal D := Finset.sum_le_sum (fun np hn=>hgb np (hU np hn))
    _=ENNReal.ofReal ((U.card:ℝ)*D) := by
      rw [←ENNReal.ofReal_sum_of_nonneg (fun _ _=>hD)]
      simp
    _≤ENNReal.ofReal ((pairCountConstant*Real.log (2+P))*D) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcard hD)
    _=_ := by congr 1; dsimp [D]; ring

lemma Admissible.good_structural_uniform_oai {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M A P : ℝ,1≤M → 0≤A → 1≤P → 1≤Real.log (2+P) →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → 0<I → I≤1 → b-a≤I → 1≤w → w≤P →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let Q := {n : ℕ×ℕ | sourceRepresentative n.1≤P ∧
        1/sourceRepresentative n.1 ≤ cappedRepresentative n.2}
      (∑'n : ℕ×ℕ,Q.indicator (fun n=>∑'nt : ℕ,∑'nr : ℕ,
        if cappedRepresentative n.2/16384 ≤ cappedRepresentative nt ∧ cappedRepresentative nt ≤ cappedRepresentative n.2/16 then
          representativeGoodCost s F zX w ![n.1,nt,n.2,nr] a b else 0) n)≤
        ENNReal.ofReal (C*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w)) := by
  classical
  obtain ⟨Cr,hCr,hregular⟩ := hd.good_regular_structural_uniform T₀
  obtain ⟨Ce,hCe,hexception⟩ := hd.good_low_uniform T₀
  refine ⟨Cr+Ce,add_nonneg hCr hCe,?_⟩
  intro M A P hM hA hP hL s T F hs hT hTT zX a b I w hzX ha hb hI hI1 hJI hw hwP HZ
  dsimp only
  let Q := {n : ℕ×ℕ | sourceRepresentative n.1≤P ∧
    1/sourceRepresentative n.1 ≤ cappedRepresentative n.2}
  let Gr := fun n : ℕ×ℕ=>∑'nt : ℕ,∑'nr : ℕ,
    if cappedRepresentative n.2/16384 ≤ cappedRepresentative nt ∧ cappedRepresentative nt ≤ cappedRepresentative n.2/16 then
      representativeRegularGoodCost s F zX P M A I w ![n.1,nt,n.2,nr] a b else 0
  let Ge := fun n : ℕ×ℕ=>∑'nt : ℕ,∑'nr : ℕ,
    if cappedRepresentative n.2/16384 ≤ cappedRepresentative nt ∧ cappedRepresentative nt ≤ cappedRepresentative n.2/16 then
      representativeLowShortGoodCost s F zX I w ![n.1,nt,n.2,nr] a b else 0
  have he (n : ℕ×ℕ) : Q.indicator (fun n=>∑'nt : ℕ,∑'nr : ℕ,
      if cappedRepresentative n.2/16384 ≤ cappedRepresentative nt ∧ cappedRepresentative nt ≤ cappedRepresentative n.2/16 then
        representativeGoodCost s F zX w ![n.1,nt,n.2,nr] a b else 0) n≤
      Q.indicator Gr n+Q.indicator Ge n := by
    by_cases hn : n∈Q
    · simp only [indicator_of_mem hn,Gr,Ge]
      rw [←ENNReal.tsum_add]
      apply ENNReal.tsum_le_tsum
      intro nt
      rw [←ENNReal.tsum_add]
      apply ENNReal.tsum_le_tsum
      intro nr
      by_cases ht : cappedRepresentative n.2/16384 ≤ cappedRepresentative nt ∧ cappedRepresentative nt ≤ cappedRepresentative n.2/16
      · simp only [ite_eq_left ht]
        by_cases hreg : regularCentralIndex P M A I w ![n.1,nt,n.2,nr]
        · have he : representativeRegularGoodCost s F zX P M A I w ![n.1,nt,n.2,nr] a b=
              representativeGoodCost s F zX w ![n.1,nt,n.2,nr] a b := ite_eq_left hreg
          rw [he]
          exact le_add_right le_rfl
        · have hh : ¬(512/min (sourceRepresentative n.1) w < cappedRepresentative n.2 ∨
              min I (stabilityLength P 16384 M A (sourceRepresentative n.1) w (cappedRepresentative n.2)) < cappedRepresentative nr) := hreg
          have hlow : cappedRepresentative n.2≤512/min (sourceRepresentative n.1) w :=
            le_of_not_gt (not_or.mp hh).1
          have hr : cappedRepresentative nr≤I := (le_of_not_gt (not_or.mp hh).2).trans (min_le_left ..)
          have he : representativeLowShortGoodCost s F zX I w ![n.1,nt,n.2,nr] a b=
              representativeGoodCost s F zX w ![n.1,nt,n.2,nr] a b := ite_eq_left ⟨hlow,hr⟩
          rw [he]
          exact le_add_left le_rfl
      · simp only [ite_eq_right ht,zero_add,le_refl]
    · simp only [indicator_of_notMem hn,zero_add,le_refl]
  change (∑'n : ℕ×ℕ,Q.indicator (fun n=>∑'nt : ℕ,∑'nr : ℕ,
    if cappedRepresentative n.2/16384 ≤ cappedRepresentative nt ∧ cappedRepresentative nt ≤ cappedRepresentative n.2/16 then
      representativeGoodCost s F zX w ![n.1,nt,n.2,nr] a b else 0) n)≤_
  apply (ENNReal.tsum_le_tsum he).trans
  rw [ENNReal.tsum_add]
  let B := P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w
  let V := I*P^2*Real.log (2+P)/w
  have hV : 0≤V := by dsimp [V]; positivity
  have hB : 0≤B := by dsimp [B]; positivity
  have hVB : V≤B := by
    have hroot := Real.sqrt_nonneg A
    have hfirst : 0≤P*Real.sqrt I := by positivity
    have ht : V≤(M+Real.sqrt A)*V := le_mul_of_one_le_left hV (by linarith)
    calc
      V≤(M+Real.sqrt A)*V := ht
      _≤P*Real.sqrt I+(M+Real.sqrt A)*V := le_add_of_nonneg_left hfirst
      _=B := by dsimp [B,V]; ring
  have hr := hregular M A P hM hA hP hL s T F hs hT hTT
    zX a b I w hzX ha hb hI hJI (zero_lt_one.trans_le hw) hwP HZ
  have he' := hexception P hP hL s T F hs hT hTT zX a b I w ha hb hI hI1 hJI hw hwP
  calc
    _≤ENNReal.ofReal (Cr*B)+ENNReal.ofReal (Ce*V) := add_le_add hr he'
    _≤ENNReal.ofReal (Cr*B)+ENNReal.ofReal (Ce*B) :=
      add_le_add le_rfl (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hVB hCe))
    _=ENNReal.ofReal ((Cr+Ce)*B) := by rw [←ENNReal.ofReal_add (mul_nonneg hCr hB) (mul_nonneg hCe hB)]; congr 1; ring

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

end

end OAI
end

theorem solution : type_of% @OAI.RVM.Admissible.good_structural_uniform_oai := @OAI.RVM.Admissible.good_structural_uniform_oai
