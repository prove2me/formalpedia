-- Prove2me | solution 1 for OAI.SubsphereRegression.normalized_routing_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:12:32.58727+00:00
-- url     : https://prove2.me/submissions/c4ae5e05-57d1-437b-b187-9f37a385cc5b

-- Generated from openai/math@1581d4c lean/OAI/Probability/Subsphere/Regression/Blocks.lean:L220-L277
-- (upload_full_project.md Phase 4): solution for node OAI.SubsphereRegression.normalized_routing_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SubsphereCurrent
import Definitions.Def_OAI_Probability_Subsphere_Models
import Definitions.Def_OAI_Probability_Subsphere_Regression_Geometry
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gram
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gaussian
import Definitions.Def_OAI_Probability_Subsphere_Regression_Projection
import Definitions.Def_OAI_Probability_Subsphere_Regression_Model
import Definitions.Def_OAI_Probability_Subsphere_Regression_Spheres
import Definitions.Def_OAI_Probability_Subsphere_Regression_Blocks
import Theorems.Thm_OAI_SubsphereRegression_exists_projection_support
import Theorems.Thm_OAI_SubsphereRegression_projectionLaw_set_bound

-- ---- from OAI.Probability.Subsphere.Regression.Blocks ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
universe u
namespace SubsphereRegression
open scoped Topology
open InnerProductSpace
open scoped Pointwise
namespace Learner
end Learner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [BorelSpace E] in
lemma replicaConstant_le {ν : Measure E} (hν : ν univ ≤ 1) {a m : ℕ}
    (hd : 1 ≤ Module.finrank ℝ E) (ha : a ≤ Module.finrank ℝ E) (hm : m ≤ Module.finrank ℝ E) :
    replicaConstant ν (a : ℝ) m ≤ (128 : ℝ≥0∞) ^ Module.finrank ℝ E := by
  let d := Module.finrank ℝ E
  have h2 : (2 : ℝ≥0∞) ≤ 2^d := by simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ≥0∞) ≤ 2) hd
  have hp : (2 : ℝ≥0∞)^(m+1) ≤ 4^d := by
    rw [pow_succ]
    calc
      _ ≤ (2 : ℝ≥0∞)^d * 2^d := mul_le_mul' (pow_le_pow_right₀ (by norm_num) hm) h2
      _ = _ := by rw [← mul_pow]; norm_num
  calc
    replicaConstant ν (a : ℝ) m ≤ 1 + (4 : ℝ≥0∞)^d * 4^d * 4^d := by
      unfold replicaConstant
      rw [Real.rpow_natCast, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num),
        ENNReal.ofReal_pow (by norm_num)]
      norm_num only [ENNReal.ofReal_ofNat]
      gcongr <;> norm_num
    _ = 1 + (64 : ℝ≥0∞)^d := by rw [mul_assoc, ← mul_pow, ← mul_pow]; norm_num
    _ ≤ (2 : ℝ≥0∞) * 64^d := by
      rw [two_mul]
      exact add_le_add (one_le_pow₀ (by norm_num)) le_rfl
    _ ≤ (2 : ℝ≥0∞)^d * 64^d := mul_le_mul' h2 le_rfl
    _ = _ := by rw [← mul_pow]; norm_num; rfl

lemma projectionLaw_uniform_set_bound {ν : Measure E} [IsFiniteMeasure ν]
    {a m n : ℕ} (hν : HasLocalMassBound ν (a : ℝ)) (hν1 : ν univ ≤ 1)
    (hsupport : ν.support ⊆ Metric.closedBall 0 1)
    (hd : 1 ≤ Module.finrank ℝ E) (ha : a ≤ Module.finrank ℝ E) (hm : m ≤ Module.finrank ℝ E)
    (hn : 1 ≤ n) (hmargin : n+m ≤ a) (S : Set ((Fin m → E) × (Fin m → ℝ))) :
    projectionLaw ν m S ≤ (128 : ℝ≥0∞) ^ Module.finrank ℝ E *
      (matrixLabelReference (E := E) m S)^(1 - 1 / ((n : ℝ)+1)) := by
  apply (projectionLaw_set_bound hν hsupport m n hn (by exact_mod_cast hmargin) S).trans
  apply mul_le_mul' _ le_rfl
  have hn0 : (0 : ℝ) < n+1 := by positivity
  calc
    _ ≤ (((128 : ℝ≥0∞)^Module.finrank ℝ E) ^ n)^(1 / ((n : ℝ)+1)) := by
      apply ENNReal.rpow_le_rpow _ (by positivity)
      simpa only [one_mul] using mul_le_mul' hν1 (pow_le_pow_left' (replicaConstant_le hν1 hd ha hm) n)
    _ = ((128 : ℝ≥0∞)^Module.finrank ℝ E)^((n : ℝ)/(n+1)) := by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      congr 1
      rw [mul_one_div]
    _ ≤ ((128 : ℝ≥0∞)^Module.finrank ℝ E)^(1 : ℝ) :=
      ENNReal.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num))
        ((div_le_one hn0).2 (by linarith))
    _ = _ := ENNReal.rpow_one _

lemma finite_rpow_holder {J : Type*} [Fintype J] (a : J → ℝ≥0∞) {q : ℝ} (hq : 1 < q) :
    (∑ j, a j ^ (1 - 1/q)) ≤
      (Fintype.card J : ℝ≥0∞)^(1/q) * (∑ j, a j)^(1-1/q) := by
  have hh := Real.HolderConjugate.conjExponent hq
  have hq' : q.conjExponent ≠ 0 := ne_of_gt hh.symm.pos
  have hex : 1 - 1/q = q.conjExponent⁻¹ := by simpa only [one_div] using hh.one_sub_inv
  rw [hex]
  simpa only [one_mul, one_div, ENNReal.one_rpow, ENNReal.rpow_inv_rpow hq',
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] using
    ENNReal.inner_le_Lp_mul_Lq Finset.univ (fun _ : J => (1 : ℝ≥0∞))
      (fun j => a j ^ q.conjExponent⁻¹) hh

lemma normalized_routing_bound {J : Type*} [Fintype J] [MeasurableSpace J]
    [MeasurableSingletonClass J] (ν : J → Measure E) [∀ j, IsFiniteMeasure (ν j)]
    {a m n : ℕ} (hν : ∀ j, HasLocalMassBound (ν j) (a : ℝ))
    (hν1 : ∀ j, ν j univ ≤ 1) (hsupport : ∀ j, (ν j).support ⊆ Metric.closedBall 0 1)
    (hd : 1 ≤ Module.finrank ℝ E) (ha : a ≤ Module.finrank ℝ E)
    (hm : m ≤ Module.finrank ℝ E) (hn : 1 ≤ n) (hmargin : n+m ≤ a)
    (φ : ((Fin m → E) × (Fin m → ℝ)) → J) (hφ : Measurable φ) :
    (∑ j, projectionLaw (ν j) m {x | φ x = j}) ≤
      (32768 : ℝ≥0∞)^Module.finrank ℝ E * (Fintype.card J : ℝ≥0∞)^(1/((n : ℝ)+1)) := by
  classical
  obtain ⟨D, hD, hDs, hDV⟩ := exists_projection_support (E := E) m hm
  let S : J → Set ((Fin m → E) × (Fin m → ℝ)) := fun j => D ∩ {x | φ x = j}
  have hS (j : J) : MeasurableSet (S j) := hD.inter (hφ (measurableSet_singleton j))
  have hSD (j : J) : projectionLaw (ν j) m (S j) = projectionLaw (ν j) m {x | φ x = j} := by
    apply Measure.measure_inter_eq_of_ae
    unfold projectionLaw
    apply (ae_map_iff (by fun_prop) hD).2
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae (ν j).support_mem_ae] with x hx
    exact hDs x.1 x.2 (by simpa using hsupport j hx)
  have hdis : Pairwise (Function.onFun Disjoint S) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hi hj
    exact hij (hi.2.symm.trans hj.2)
  have hUnion : (⋃ j, S j) = D := by
    ext x
    simp only [S, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    exact ⟨fun ⟨_,h,_⟩ => h, fun h => ⟨φ x,h,rfl⟩⟩
  have hsum : ∑ j, matrixLabelReference (E := E) m (S j) = matrixLabelReference (E := E) m D := by
    simpa only [hUnion, tsum_fintype] using (measure_iUnion (μ := matrixLabelReference (E := E) m) hdis hS).symm
  have hα : 0 ≤ 1 - 1/((n : ℝ)+1) := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) (by linarith : (1 : ℝ) ≤ n+1)]
  have hV : (matrixLabelReference (E := E) m D)^(1-1/((n : ℝ)+1)) ≤
      (256 : ℝ≥0∞)^Module.finrank ℝ E := by
    calc
      _ ≤ ((256 : ℝ≥0∞)^Module.finrank ℝ E)^(1-1/((n : ℝ)+1)) :=
        ENNReal.rpow_le_rpow (hDV.trans (pow_le_pow_left' (by norm_num) _)) hα
      _ ≤ ((256 : ℝ≥0∞)^Module.finrank ℝ E)^ (1 : ℝ) :=
        ENNReal.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) (sub_le_self _ (by positivity))
      _ = _ := ENNReal.rpow_one _
  calc
    _ = ∑ j, projectionLaw (ν j) m (S j) := by simp_rw [hSD]
    _ ≤ ∑ j, (128 : ℝ≥0∞)^Module.finrank ℝ E *
        (matrixLabelReference (E := E) m (S j))^(1-1/((n : ℝ)+1)) :=
      Finset.sum_le_sum fun j _ => projectionLaw_uniform_set_bound
        (hν j) (hν1 j) (hsupport j) hd ha hm hn hmargin (S j)
    _ = (128 : ℝ≥0∞)^Module.finrank ℝ E *
        ∑ j, (matrixLabelReference (E := E) m (S j))^(1-1/((n : ℝ)+1)) := by rw [Finset.mul_sum]
    _ ≤ (128 : ℝ≥0∞)^Module.finrank ℝ E *
        ((Fintype.card J : ℝ≥0∞)^(1/((n : ℝ)+1)) *
         (∑ j, matrixLabelReference (E := E) m (S j))^(1-1/((n : ℝ)+1))) :=
      mul_le_mul' le_rfl (finite_rpow_holder _ (by exact_mod_cast Nat.lt_add_one_of_le hn))
    _ ≤ (128 : ℝ≥0∞)^Module.finrank ℝ E *
        ((Fintype.card J : ℝ≥0∞)^(1/((n : ℝ)+1)) * (256 : ℝ≥0∞)^Module.finrank ℝ E) := by
      rw [hsum]
      exact mul_le_mul' le_rfl (mul_le_mul' le_rfl hV)
    _ = _ := by rw [mul_left_comm, ← mul_pow]; norm_num; rw [mul_comm]

end SubsphereRegression

end

end OAI

-- ---- platform node ----
open OAI OAI.SubsphereRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
open scoped Topology
open InnerProductSpace
open scoped Pointwise


theorem solution : type_of% @_root_.OAI.SubsphereRegression.normalized_routing_bound := @_root_.OAI.SubsphereRegression.normalized_routing_bound
