-- Prove2me | solution 1 for OAI.SKGapCutoff.Recipe.gibbs_residual_selection_deficit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:04:43.911175+00:00
-- url     : https://prove2.me/submissions/235ebe2b-4a08-4518-96cc-ca07c6549976

import Mathlib
import Definitions.Def_OAIQ072A002
import Theorems.Thm_OAI_SKGapCutoff_Recipe_gibbs_residual_selection_tail

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_Operation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Matrix
variable {n : ℕ}

lemma vectorNorm_sq (u : Fin n→ℝ) : vectorNorm u^2=∑i,(u i)^2 := by
  exact EuclideanSpace.real_norm_sq_eq _

lemma vectorNorm_nonneg (u : Fin n→ℝ) : 0 ≤ vectorNorm u := norm_nonneg _

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Matrix
variable {n : ℕ}

lemma vectorNorm_add (u v : Fin n→ℝ) :
    vectorNorm (u+v) ≤ vectorNorm u+vectorNorm v := by
  exact norm_add_le (WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 v)

lemma vectorNorm_mono {u v : Fin n→ℝ} (h : ∀i,|u i|≤|v i|) : vectorNorm u ≤ vectorNorm v := by
  apply nonneg_le_nonneg_of_sq_le_sq (vectorNorm_nonneg _)
  simp only [←sq,vectorNorm_sq]
  exact Finset.sum_le_sum fun i _=>by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (u i)) (h i) 2

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_ImplicitCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary
variable {n : ℕ}

lemma vectorNorm_const (c : ℝ) : vectorNorm (fun _ : Fin n=>c)=|c| *Real.sqrt n := by
  apply (sq_eq_sq₀ (vectorNorm_nonneg _) (by positivity)).mp
  rw [vectorNorm_sq,mul_pow,sq_abs,Real.sq_sqrt (Nat.cast_nonneg n)]
  simp [mul_comm]

lemma vectorNorm_neg (v : Fin n→ℝ) : vectorNorm (-v)=vectorNorm v := by
  exact norm_neg (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))
lemma vectorNorm_sub (u v : Fin n→ℝ) : vectorNorm (u-v)≤vectorNorm u+vectorNorm v := by
  simpa only [sub_eq_add_neg,vectorNorm_neg] using vectorNorm_add u (-v)
lemma vectorNorm_tanh (z : Fin n→ℝ) : vectorNorm (fun i=>Real.tanh (z i))≤Real.sqrt n := by
  simpa only [vectorNorm_const,abs_one,one_mul] using
    (vectorNorm_mono (u:=fun i=>Real.tanh (z i)) (v:=fun _=>1)
      (fun i=>by simpa using (Real.abs_tanh_lt_one (z i)).le))

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_ConditionalMean
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open scoped BigOperators NNReal ENNReal
open MeasureTheory Metric Set
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal ENNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Set
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Matrix
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open scoped BigOperators
namespace SKGapCutoff.Static

lemma conditionalMean_abs_le {n : ℕ} (Q : Spin n → ℝ)
    (hQ : ∀ x, 0 ≤ Q x) (x : Spin n) (i : Fin n) :
    |conditionalMean Q x i| ≤ 1 := by
  have hs : |spin x i| = 1 := by cases hx : x i <;> simp [spin,hx]
  simp only [conditionalMean, abs_mul, hs, one_mul, abs_div]
  rw [abs_of_nonneg (add_nonneg (hQ x) (hQ _))]
  apply div_le_one_of_le₀ _ (add_nonneg (hQ x) (hQ _))
  exact abs_sub_le_iff.2 ⟨by linarith [hQ (flip x i)], by linarith [hQ x]⟩

lemma weighted_cauchy_sq {α : Type*} [Fintype α] (w f g : α → ℝ)
    (hw : ∀ a, 0 ≤ w a) :
    (∑ a, w a*f a*g a)^2 ≤ (∑ a, w a*f a^2)*(∑ a, w a*g a^2) := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    Finset.univ (fun a _ => mul_nonneg (hw a) (sq_nonneg _))
      (fun a _ => mul_nonneg (hw a) (sq_nonneg _))
  intro a _
  exact le_of_eq (by ring)

end SKGapCutoff.Static

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise NNReal ENNReal

end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_WeakResidual
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Static
variable {n : ℕ}

lemma conditionalVariance_nonneg (P : Spin n→ℝ) (hP : ∀ x,0≤P x)
    (x : Spin n) (i : Fin n) : 0 ≤ conditionalVariance P x i := by
  have h:=conditionalMean_abs_le P hP x i
  have hh:=pow_le_pow_left₀ (abs_nonneg (conditionalMean P x i)) h 2
  simpa only [sq_abs,one_pow,conditionalVariance,sub_nonneg] using hh

lemma varianceEnergy_nonneg (P : Spin n→ℝ) (hP : ∀ x,0≤P x) (f : Observables n) :
    0≤varianceEnergy P f := by
  exact Finset.sum_nonneg (fun x _=>mul_nonneg (hP x)
    (Finset.sum_nonneg (fun i _=>mul_nonneg (conditionalVariance_nonneg P hP x i) (sq_nonneg _))))

end SKGapCutoff.Static

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_ResidualMultiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Static
variable {n : ℕ}

lemma starSquared_nonneg (P : Spin n→ℝ) (hP : ∀x,0≤P x) (f : Observables n) :
    0≤ starSquared P f := add_nonneg (Finset.sum_nonneg fun x _=>mul_nonneg (hP x) (sq_nonneg _))
      (varianceEnergy_nonneg P hP f)

end SKGapCutoff.Static

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Terminal_FieldGibbs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff
variable {n : ℕ}

lemma fieldPartition_pos (J : Interaction n) (h : Fin n→ℝ) : 0<fieldPartition J h :=
  Finset.sum_pos (fun _ _=>Real.exp_pos _) Finset.univ_nonempty
lemma fieldGibbs_pos (J : Interaction n) (h : Fin n→ℝ) (x : Spin n) : 0<fieldGibbs J h x :=
  div_pos (Real.exp_pos _) (fieldPartition_pos J h)
end SKGapCutoff

end
end

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Matrix
variable {n : ℕ}

lemma vectorPair_abs (U V : VectorFields n) (x : Spin n) :
    |vectorPair U V x| ≤ vectorNorm (U x)*vectorNorm (V x) := by
  simpa [vectorPair,vectorNorm,EuclideanSpace.inner_eq_star_dotProduct,dotProduct,mul_comm] using
    abs_real_inner_le_norm (WithLp.toLp 2 (U x) : EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 (V x))

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_SmoothSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal ContDiff
namespace SKGapCutoff.Recipe
open Primary Static
variable {n : ℕ}

lemma residualScalarCutoff_bounds (u : ℝ) :
    0 ≤ residualScalarCutoff u ∧ residualScalarCutoff u≤1 := by
  refine ⟨mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _),?_⟩
  exact (mul_le_mul (Real.smoothTransition.le_one _) (Real.smoothTransition.le_one _)
    (Real.smoothTransition.nonneg _) (by norm_num)).trans_eq (by simp)

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators NNReal
namespace SKGapCutoff.Recipe
open Primary Static
variable {n : ℕ}

lemma residualStepCutoff_bounds (ρ j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) (x : Spin n) :
    0 ≤ residualStepCutoff ρ j J h k x ∧ residualStepCutoff ρ j J h k x≤1 := residualScalarCutoff_bounds _
lemma residualCutoff_bounds (ρ j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) (x : Spin n) :
    0 ≤ residualCutoff ρ j J h k x ∧ residualCutoff ρ j J h k x≤1 := by
  have h0:=residualStepCutoff_bounds ρ j J h k x
  have h1:=residualStepCutoff_bounds ρ j J h (k+1) x
  exact ⟨mul_nonneg h0.1 h1.1,(mul_le_mul h0.2 h1.2 h1.1 (by norm_num)).trans_eq (by simp)⟩

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_SelectionPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary Static
variable {n : ℕ}

lemma cutoffDeficit_prod (C : ℕ→ℝ) (d : ℕ) :
    cutoffDeficit C d=∏k∈Finset.range d,(1-C k) := by
  induction d with
  | zero=>simp [cutoffDeficit]
  | succ d ih=>
    simp only [cutoffDeficit,Finset.sum_range_succ] at ih ⊢
    rw [Finset.prod_range_succ,cutoffWeight,←ih]
    ring

lemma cutoffDeficit_bounds (C : ℕ→ℝ) (d : ℕ) (hC : ∀k,0≤C k ∧ C k≤1) :
    0 ≤ cutoffDeficit C d ∧ cutoffDeficit C d≤1 := by
  rw [cutoffDeficit_prod]
  refine ⟨Finset.prod_nonneg (fun k _=>sub_nonneg.mpr (hC k).2),?_⟩
  exact Finset.prod_le_one (fun k _=>sub_nonneg.mpr (hC k).2) (fun k _=>by linarith [(hC k).1])

universe u

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_LocalExtraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Static
variable {n : ℕ}

lemma tested_l2_to_star (P G H : Observables n) (hP : ∀x,0≤P x)
    {D : ℝ} (hD : 0≤D) (hH : (∑x,P x*(H x)^2)≤D) :
    |∑x,P x*G x*H x|≤Real.sqrt D*starNorm P G := by
  have hG : 0≤∑x,P x*(G x)^2:=Finset.sum_nonneg fun x _=>mul_nonneg (hP x) (sq_nonneg _)
  have hS : (∑x,P x*(G x)^2)≤ starSquared P G :=
    le_add_of_nonneg_right (varianceEnergy_nonneg P hP G)
  have H':=(weighted_cauchy_sq P G H hP).trans
    (mul_le_mul hS hH (Finset.sum_nonneg fun x _=>mul_nonneg (hP x) (sq_nonneg _))
      (starSquared_nonneg P hP G))
  have H'' := Real.sqrt_le_sqrt H'
  rw [Real.sqrt_sq_eq_abs,mul_comm (starSquared P G) D,Real.sqrt_mul hD] at H''
  exact H''

end SKGapCutoff.Static

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_SelectionDeficit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary Static
variable {n : ℕ}

lemma selection_deficit_l2 (hn : 0<n) (P H : Observables n) (C : ℕ→Observables n)
    (d : ℕ) (hP : ∀x,0≤P x) (hC : ∀k x,0≤C k x ∧ C k x≤1)
    {B T : ℝ} (hB : 0≤B) (hH : ∀x,|H x|≤B*Real.sqrt (n:ℝ))
    (ht : (∑x,if 0 < cutoffDeficit (fun k=>C k x) d then P x else 0)≤T/(n:ℝ)) :
    (∑x,P x*(cutoffDeficit (fun k=>C k x) d*H x)^2)≤B^2*T := by
  classical
  let D:=fun x=>cutoffDeficit (fun k=>C k x) d
  have hD x : 0≤D x ∧ D x≤1:=cutoffDeficit_bounds _ _ (fun k=>hC k x)
  have hn0 : (n:ℝ)≠0:=ne_of_gt (Nat.cast_pos.mpr hn)
  calc
    _ ≤ ∑x,(if 0<D x then P x else 0)*(B^2*(n:ℝ)) := by
      apply Finset.sum_le_sum
      intro x _
      change P x*(D x*H x)^2≤_
      by_cases hd:0<D x
      · rw [ite_eq_left hd]
        apply mul_le_mul_of_nonneg_left _ (hP x)
        have h1 : |D x*H x|≤B*Real.sqrt (n:ℝ) := by
          rw [abs_mul,abs_of_nonneg (hD x).1]
          exact (mul_le_mul_of_nonneg_left (hH x) (hD x).1).trans
            (mul_le_of_le_one_left (mul_nonneg hB (Real.sqrt_nonneg _)) (hD x).2)
        have h2:=pow_le_pow_left₀ (abs_nonneg _) h1 2
        simpa only [sq_abs,mul_pow,Real.sq_sqrt (Nat.cast_nonneg n)] using h2
      · have hz:D x=0:=le_antisymm (le_of_not_gt hd) (hD x).1
        simp [hz]
    _ = (∑x,if 0<D x then P x else 0)*(B^2*(n:ℝ)) := (Finset.sum_mul ..).symm
    _ ≤ (T/(n:ℝ))*(B^2*(n:ℝ)) :=
      mul_le_mul_of_nonneg_right ht (mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
    _ = _ := by field_simp

lemma spin_root_direction_size (r e : Fin n→ℝ) (he : vectorNorm e≤1) (x : Spin n) :
    |∑i,(spin x i-Real.tanh (r i))*e i|≤2*Real.sqrt (n:ℝ) := by
  have hv : vectorNorm (fun i=>spin x i-Real.tanh (r i))≤2*Real.sqrt (n:ℝ) := by
    apply (vectorNorm_sub (spin x) (fun i=>Real.tanh (r i))).trans
    have hs : vectorNorm (spin x)≤Real.sqrt (n:ℝ) := by
      simpa only [vectorNorm_const,abs_one,one_mul] using
        (vectorNorm_mono (u:=spin x) (v:=fun _=>1) (fun i=>by simp [spin];split_ifs <;> norm_num))
    exact (add_le_add hs (vectorNorm_tanh r)).trans_eq (by ring)
  have hpair:=vectorPair_abs (fun _ : Spin n=>fun i=>spin x i-Real.tanh (r i)) (fun _=>e) x
  change |∑i,(spin x i-Real.tanh (r i))*e i|≤_ at hpair
  exact hpair.trans ((mul_le_mul hv he (vectorNorm_nonneg _) (by positivity)).trans_eq (mul_one _))

universe u
variable {Ω : Type u} {N : Ω→ℕ} {j R B W C ρ ε : ℝ}
variable {J : ∀a,Interaction (N a)} {h : ∀a,Fin (N a)→ℝ}

theorem gibbs_residual_selection_deficit_oai (m : ℕ) (hρ : 0<ρ) (hε : 0<ε)
    (hm : 2<(m:ℝ)*ρ^2/4) (he : 2*(2*m:ℕ)*ε≤1)
    (hR : 0≤R) (hB : 0≤B) (hW : 0≤W) (hC : 0≤C)
    (hn : ∀a,0<N a) (hJ : ∀a,(J a).IsSymm) (hdiag : ∀a i,J a i i=0)
    (hevent : ∀a,RecipeMatrixEvent j R (residualCoefficientBudget j 2 (2*m) 0) B W C (2*m+1) (2*(2*m)) (J a)) :
    ∃D≥0,∀a (r e : Fin (N a)→ℝ),vectorNorm e≤1→∀G : Observables (N a),
      |∑x,fieldGibbs (J a) (h a) x*G x*
        (cutoffDeficit (fun k=>residualCutoff ρ j (J a) (h a) k x) (2*m-1)*
          (∑i,(spin x i-Real.tanh (r i))*e i))|≤D*starNorm (fieldGibbs (J a) (h a)) G := by
  obtain ⟨T,U,hT,hU,ht⟩:=gibbs_residual_selection_tail (h:=h) m hρ hε hm he hR hB hW hC hn hJ hdiag hevent
  refine ⟨Real.sqrt (2^2*T),Real.sqrt_nonneg _,?_⟩
  intro a r e he G
  apply tested_l2_to_star _ _ _ (fun x=>(fieldGibbs_pos _ _ _).le) (by positivity)
  exact selection_deficit_l2 (hn a) _ _ _ (2*m-1) (fun x=>(fieldGibbs_pos _ _ _).le)
    (fun k x=>residualCutoff_bounds ρ j (J a) (h a) k x) (by norm_num)
    (spin_root_direction_size r e he) (ht a).1

end SKGapCutoff.Recipe

end
end

end OAI
end

theorem solution.{u} : type_of% @OAI.SKGapCutoff.Recipe.gibbs_residual_selection_deficit_oai.{u} := @OAI.SKGapCutoff.Recipe.gibbs_residual_selection_deficit_oai.{u}
