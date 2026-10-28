-- Prove2me | solution 1 for OAI.RVM.remaining_stable_source_angular
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:44:34.448644+00:00
-- url     : https://prove2.me/submissions/25706c9b-89a9-4673-803f-ae637c2800f0

import Mathlib
import Definitions.Def_OAIQ073V000

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

lemma relativeSourceAngle_nonneg {θ φ σ : ℝ} (hθ : 0≤θ) (hφ : 0≤φ) (hσ : 0<σ) :
    0 ≤ relativeSourceAngle θ φ σ := by
  dsimp [relativeSourceAngle]
  positivity

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

lemma remaining_magnetic_fixed_receiver_sum {φ K κ β : ℝ} (hφ : 0≤φ)
    (hK : 0<K) (hκ : 0≤κ) (hβ : 0≤β) (hβ1 : β≤1/2)
    (Sθ : Finset ℕ) (Sσ : ℕ→Finset ℕ)
    (hθ : ∀i∈Sθ,φ≤κ*cappedRepresentative i)
    (hσ : ∀i∈Sθ,∀j∈Sσ i,cappedRepresentative j≤K*cappedRepresentative i) :
    ∑i∈Sθ,∑j∈Sσ i,
      relativeSourceAngle (cappedRepresentative i) φ (cappedRepresentative j)/(cappedRepresentative j)^β ≤
    relativeAngularConstant K κ (3/2-β)*(1-((2:ℝ)⁻¹)^(3/2-β))⁻¹ := by
  let C := relativeAngularConstant K κ (3/2-β)
  have hC : 0≤C := relativeAngularConstant_nonneg hK.le hκ (by linarith)
  have hs := capped_positive_power_sum_unscaled (by norm_num : (0:ℝ)<1)
    (show 0<(3/2:ℝ)-β by linarith) Sθ (fun _ _=>cappedRepresentative_le_one _)
  rw [Real.one_rpow,mul_one] at hs
  calc
    _ ≤ ∑i∈Sθ,C*(cappedRepresentative i)^(3/2-β) := by
      apply Finset.sum_le_sum
      intro i hi
      exact relative_source_angle_sum (cappedRepresentative_pos i) hφ hK hκ hβ hβ1 (hθ i hi) (Sσ i) (hσ i hi)
    _ = C*(∑i∈Sθ,(cappedRepresentative i)^(3/2-β)) := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hs hC

lemma square_root_clipped_stability {I P C M A p w σ : ℝ}
    (hI : 0<I) (hP : 0<P) (hC : 0<C) (hM : 0<M) (hA : 0≤A)
    (hp : 0<p) (hw : 0<w) (hσ : 0<σ) (hσ1 : σ≤1) :
    Real.sqrt (Real.sqrt (1+I/min I (stabilityLength P C M A p w σ/2))) ≤
      2+2*Real.sqrt C*(I : ℝ)^(1/4:ℝ)*Real.sqrt (P/min p w)*
        (Real.sqrt M+Real.sqrt (Real.sqrt (A*Real.log (2+P))))/Real.sqrt σ := by
  have hL : 0≤Real.log (2+P) := Real.log_nonneg (by linarith)
  have hm : 0 < min p w := lt_min hp hw
  have hlam := stabilityLength_pos hP hC hM hp hw hσ (A:=A)
  have hr := sqrt_baseline_clipped_length hI hlam
  rw [sqrt_div_stabilityLength hP.le hC.le hM.le hp.le hw.le hσ.le hI.le] at hr
  have hroot : Real.sqrt σ≤1 := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hσ1
  have hs : σ≤Real.sqrt σ := by
    nlinarith [Real.sq_sqrt hσ.le,Real.sqrt_nonneg σ]
  have hrate : stabilityRate P C M A p w σ ≤
      C*(P/min p w)*(M+Real.sqrt (A*Real.log (2+P)))/σ := by
    unfold stabilityRate
    rw [Real.sqrt_div (mul_nonneg hA hL)]
    have hdiv : Real.sqrt (A*Real.log (2+P))/Real.sqrt σ≤
        Real.sqrt (A*Real.log (2+P))/σ :=
      div_le_div_of_nonneg_left (Real.sqrt_nonneg _) hσ hs
    have he : C*(P/min p w)*(M/σ+Real.sqrt (A*Real.log (2+P))/σ)=
        C*(P/min p w)*(M+Real.sqrt (A*Real.log (2+P)))/σ := by ring
    rw [←he]
    exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hdiv) (by positivity)
  have hX : 0≤Real.sqrt I*stabilityRate P C M A p w σ := by
    unfold stabilityRate
    positivity
  have hsimple : Real.sqrt (2*(1+Real.sqrt I*stabilityRate P C M A p w σ))≤
      2+2*Real.sqrt (Real.sqrt I*stabilityRate P C M A p w σ) := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · nlinarith [Real.sq_sqrt hX,Real.sqrt_nonneg (Real.sqrt I*stabilityRate P C M A p w σ)]
  have hII : Real.sqrt (Real.sqrt I)=(I : ℝ)^(1/4:ℝ) := by
    rw [Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,←Real.rpow_mul hI.le]
    congr 1
    norm_num
  have hfac : Real.sqrt (Real.sqrt I*(C*(P/min p w)*(M+Real.sqrt (A*Real.log (2+P)))/σ))=
      Real.sqrt C*(I : ℝ)^(1/4:ℝ)*Real.sqrt (P/min p w)*
        Real.sqrt (M+Real.sqrt (A*Real.log (2+P)))/Real.sqrt σ := by
    rw [Real.sqrt_mul (Real.sqrt_nonneg I),Real.sqrt_div (by positivity),
      Real.sqrt_mul (by positivity : 0≤C*(P/min p w)),Real.sqrt_mul hC.le,hII]
    ring
  calc
    _≤Real.sqrt (2*(1+Real.sqrt I*stabilityRate P C M A p w σ)) := Real.sqrt_le_sqrt hr
    _≤2+2*Real.sqrt (Real.sqrt I*stabilityRate P C M A p w σ) := hsimple
    _≤2+2*Real.sqrt (Real.sqrt I*(C*(P/min p w)*(M+Real.sqrt (A*Real.log (2+P)))/σ)) := by gcongr
    _=2+2*(Real.sqrt C*(I : ℝ)^(1/4:ℝ)*Real.sqrt (P/min p w)*
        Real.sqrt (M+Real.sqrt (A*Real.log (2+P)))/Real.sqrt σ) := by rw [hfac]
    _≤2+2*(Real.sqrt C*(I : ℝ)^(1/4:ℝ)*Real.sqrt (P/min p w)*
        (Real.sqrt M+Real.sqrt (Real.sqrt (A*Real.log (2+P))))/Real.sqrt σ) := by
      have hadd : Real.sqrt (M+Real.sqrt (A*Real.log (2+P)))≤
          Real.sqrt M+Real.sqrt (Real.sqrt (A*Real.log (2+P))) := by
        apply Real.sqrt_le_iff.mpr
        constructor
        · positivity
        · nlinarith [Real.sq_sqrt hM.le,Real.sq_sqrt (Real.sqrt_nonneg (A*Real.log (2+P))),
            mul_nonneg (Real.sqrt_nonneg M) (Real.sqrt_nonneg (Real.sqrt (A*Real.log (2+P))))]
      gcongr
    _=_ := by ring

lemma remaining_shared_source_angular {φ K κ B g b : ℝ} (hφ : 0<φ)
    (hK : 0<K) (hκ : 0<κ) (hB : 0≤B) (hg : 0≤g) (hb : 0≤b)
    (R : ℕ→ℝ) (hR : ∀j,R j≤2+B/Real.sqrt (cappedRepresentative j))
    (Sθ : Finset ℕ) (Sσ : ℕ→Finset ℕ)
    (hθ : ∀i∈Sθ,φ≤κ*cappedRepresentative i)
    (hσ : ∀i∈Sθ,∀j∈Sσ i,cappedRepresentative j≤K*cappedRepresentative i) :
    ∑i∈Sθ,∑j∈Sσ i,R j*relativeSourceAngle (cappedRepresentative i) φ (cappedRepresentative j)*
      (g*(φ/(cappedRepresentative i)^2)+b) ≤
    g*(2*remainingGoodConstant K κ 0*Real.sqrt φ+B*remainingGoodConstant K κ (1/2))+
    b*(2*remainingMagneticConstant K κ 0+B*remainingMagneticConstant K κ (1/2)) := by
  let G (β : ℝ) := ∑i∈Sθ,∑j∈Sσ i,(φ/(cappedRepresentative i)^2)*
    (relativeSourceAngle (cappedRepresentative i) φ (cappedRepresentative j)/(cappedRepresentative j)^β)
  let H (β : ℝ) := ∑i∈Sθ,∑j∈Sσ i,
    relativeSourceAngle (cappedRepresentative i) φ (cappedRepresentative j)/(cappedRepresentative j)^β
  have hG0 : G 0 ≤ remainingGoodConstant K κ 0*Real.sqrt φ := by
    simpa only [G,remainingGoodConstant,add_zero,sub_zero,Real.sqrt_eq_rpow] using
      remaining_good_fixed_receiver_sum hφ hK hκ (by norm_num : (0:ℝ)≤0) (by norm_num) Sθ Sσ hθ hσ
  have hG1 : G (1/2) ≤ remainingGoodConstant K κ (1/2) := by
    have hh := remaining_good_fixed_receiver_sum hφ hK hκ (by norm_num : (0:ℝ)≤1/2) (by norm_num) Sθ Sσ hθ hσ
    simpa only [G,remainingGoodConstant,sub_self,Real.rpow_zero,mul_one] using hh
  have hH0 : H 0 ≤ remainingMagneticConstant K κ 0 :=
    remaining_magnetic_fixed_receiver_sum hφ.le hK hκ.le (by norm_num) (by norm_num) Sθ Sσ hθ hσ
  have hH1 : H (1/2) ≤ remainingMagneticConstant K κ (1/2) :=
    remaining_magnetic_fixed_receiver_sum hφ.le hK hκ.le (by norm_num) (by norm_num) Sθ Sσ hθ hσ
  calc
    _≤∑i∈Sθ,∑j∈Sσ i,(2+B/Real.sqrt (cappedRepresentative j))*
      relativeSourceAngle (cappedRepresentative i) φ (cappedRepresentative j)*
        (g*(φ/(cappedRepresentative i)^2)+b) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right (hR j)
        (relativeSourceAngle_nonneg (cappedRepresentative_pos i).le hφ.le (cappedRepresentative_pos j))
    _=g*(2*G 0+B*G (1/2))+b*(2*H 0+B*H (1/2)) := by
      simp only [G,H,Real.rpow_zero,div_one,←Real.sqrt_eq_rpow,mul_add,
        Finset.mul_sum,←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _≤_ := by
      have hgg := add_le_add (mul_le_mul_of_nonneg_left hG0 (by norm_num : (0:ℝ)≤2))
        (mul_le_mul_of_nonneg_left hG1 hB)
      have hhh := add_le_add (mul_le_mul_of_nonneg_left hH0 (by norm_num : (0:ℝ)≤2))
        (mul_le_mul_of_nonneg_left hH1 hB)
      have hh := add_le_add (mul_le_mul_of_nonneg_left hgg hg) (mul_le_mul_of_nonneg_left hhh hb)
      simpa only [mul_assoc] using hh

lemma remaining_stable_source_angular_oai {I P C M A p w φ K κ g b : ℝ}
    (hI : 0<I) (hP : 0<P) (hC : 0<C) (hM : 0<M) (hA : 0≤A)
    (hp : 0<p) (hw : 0<w) (hφ : 0<φ) (hK : 0<K) (hκ : 0<κ)
    (hg : 0≤g) (hb : 0≤b)
    (Sθ : Finset ℕ) (Sσ : ℕ→Finset ℕ)
    (hθ : ∀i∈Sθ,φ≤κ*cappedRepresentative i)
    (hσ : ∀i∈Sθ,∀j∈Sσ i,cappedRepresentative j≤K*cappedRepresentative i) :
    let B := 2*Real.sqrt C*(I : ℝ)^(1/4:ℝ)*Real.sqrt (P/min p w)*
      (Real.sqrt M+Real.sqrt (Real.sqrt (A*Real.log (2+P))))
    ∑i∈Sθ,∑j∈Sσ i,
      Real.sqrt (Real.sqrt (1+I/min I (stabilityLength P C M A p w (cappedRepresentative j)/2)))*
        relativeSourceAngle (cappedRepresentative i) φ (cappedRepresentative j)*
          (g*(φ/(cappedRepresentative i)^2)+b) ≤
    g*(2*remainingGoodConstant K κ 0*Real.sqrt φ+B*remainingGoodConstant K κ (1/2))+
    b*(2*remainingMagneticConstant K κ 0+B*remainingMagneticConstant K κ (1/2)) := by
  apply remaining_shared_source_angular hφ hK hκ (by positivity) hg hb _ _ Sθ Sσ hθ hσ
  intro j
  exact square_root_clipped_stability hI hP hC hM hA hp hw (cappedRepresentative_pos j)
    (cappedRepresentative_le_one j)


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

theorem solution : type_of% @OAI.RVM.remaining_stable_source_angular_oai := @OAI.RVM.remaining_stable_source_angular_oai
