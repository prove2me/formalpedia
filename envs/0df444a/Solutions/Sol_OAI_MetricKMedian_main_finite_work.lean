-- Prove2me | solution 1 for OAI.MetricKMedian.main_finite_work
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T11:37:30.444396+00:00
-- url     : https://prove2.me/submissions/354dd989-c955-4e9c-96e7-90506a9c0931

import Mathlib
import Definitions.Def_MetricKMedian
import Definitions.Def_OAIQ035K076
import Theorems.Thm_OAI_MetricKMedian_Instance_computedPseudo_spec_s35
import Theorems.Thm_OAI_MetricKMedian_Preparation_exists_rational_all_parameters_s35
import Theorems.Thm_OAI_MetricKMedian_Reduction_Program_ordinarySet_spec_s35

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BooleanPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.Binary
open Turing Polynomial

namespace PolyProgram
variable {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool}
variable {f : α → β} {g : β → γ}

 theorem finite_work (P : PolyProgram ea eb f) (k : P.stock.tm.K) : Finite (P.stock.tm.Γ k) :=
  inferInstanceAs (Finite Bool)

end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_ApproximationSlack
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian

 theorem threshold_bounds : 1 < 1+2/Real.exp 1 ∧ 1+2/Real.exp 1 ≤ 3 := by
  have he : 0 < Real.exp 1 := Real.exp_pos _
  have he1 : 1 ≤ Real.exp 1 := by exact Real.one_le_exp (by norm_num)
  have h := (div_le_iff₀ he).mpr (show (2:ℝ) ≤ 2*Real.exp 1 by linarith only [he1])
  exact ⟨lt_add_of_pos_right 1 (div_pos (by norm_num) he),by linarith only [h]⟩

 theorem slack_product (A s t : ℝ) (hA0 : 0 ≤ A) (hA : A ≤ 3)
    (hs : 0 ≤ s) (hs1 : s ≤ 1/2) (ht : 0 ≤ t) (ht1 : t ≤ s) :
    ((A+s)/(1-s))*(1+s)*(1+t) ≤ A+41*s := by
  have hden : 0 < 1-s := by linarith only [hs1]
  have hd : (A+s)/(1-s) ≤ A+8*s := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [mul_nonneg hs (show 0 ≤ 7-A-8*s by linarith only [hA,hs1])]
  have hss : s*s ≤ s := by nlinarith
  have hsq : (1+s)*(1+s) ≤ 1+3*s := by nlinarith
  calc
    _  ≤  (A+8*s)*(1+s)*(1+t) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hd (by linarith only [hs])) (by linarith only [ht])
    _  ≤  (A+8*s)*((1+s)*(1+s)) := by
      rw [← mul_assoc]
      apply mul_le_mul_of_nonneg_left (by linarith only [ht1])
      exact mul_nonneg (by linarith only [hA0,hs]) (by linarith only [hs])
    _  ≤  (A+8*s)*(1+3*s) := mul_le_mul_of_nonneg_left hsq (by linarith only [hA0,hs])
    _  ≤  A+41*s := by
      have hAs := mul_le_mul_of_nonneg_right hA hs
      nlinarith only [hss,hAs]

 theorem exists_approximation_slack (ε : ℝ) (hε : 0 < ε) :
    ∃ (s : ℝ) (r : ℕ), 0 < s ∧ s < 1 ∧ 0 < r ∧
      1 < ((1+2/Real.exp 1+s)/(1-s))*(1+s)*(1+3/(r:ℝ)) ∧
      ((1+2/Real.exp 1+s)/(1-s))*(1+s)*(1+3/(r:ℝ))+ε/2 ≤ 1+2/Real.exp 1+ε := by
  let s := min (1/2:ℝ) (ε/100)
  have hs : 0 < s := lt_min (by norm_num) (by positivity)
  have hs1 : s ≤ 1/2 := min_le_left _ _
  have hsε : s ≤ ε/100 := min_le_right _ _
  obtain ⟨r,hr⟩ := exists_nat_gt (3/s)
  have hrR : 0 < (r:ℝ) := lt_trans (by positivity) hr
  have hrN : 0 < r := by exact_mod_cast hrR
  have ht : 3/(r:ℝ) ≤ s := (div_le_iff₀ hrR).mpr (by
    have hh := (div_lt_iff₀ hs).mp hr
    linarith only [hh])
  obtain ⟨hA,hA3⟩ := threshold_bounds
  have hp := slack_product (1+2/Real.exp 1) s (3/(r:ℝ)) (by linarith only [hA]) hA3 hs.le hs1
    (by positivity) ht
  have hbase : 1 < (1+2/Real.exp 1+s)/(1-s) := by
    apply (lt_div_iff₀ (by linarith only [hs1])).mpr
    linarith only [hA,hs]
  have hmul : 1 < ((1+2/Real.exp 1+s)/(1-s))*(1+s)*(1+3/(r:ℝ)) := by
    have ht0 : 0 ≤ 3/(r:ℝ) := by positivity
    have hp1 : 1 < ((1+2/Real.exp 1+s)/(1-s))*(1+s) := by nlinarith only [hbase,hs]
    nlinarith only [hp1,ht0]
  exact ⟨s,r,hs,by linarith only [hs1],hrN,hmul,by linarith only [hp,hsε,hε]⟩

end MetricKMedian
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Reduction_ReductionClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
section
namespace MetricKMedian.Reduction

theorem reduction_parameters (α η : ℝ) (hα : 1 < α) (hη : 0 < η) (c : ℕ) (hc : 0 < c) :
    ∃ (δ : ℚ) (a b : ℕ), 0 < (δ:ℝ) ∧ (δ:ℝ) ≤ 1/6 ∧
      1+12*(δ:ℝ) ≤ α+η ∧
      (3/2:ℝ) ≤ a*((δ:ℝ)*η/(2*c)) ∧
      6*(α+η)*c/((δ:ℝ)*η) ≤ (b:ℝ) := by
  have hsmall : (0:ℝ) < min (1/6) ((α-1)/12) := by
    apply lt_min
    · norm_num
    · exact div_pos (sub_pos.mpr hα) (by norm_num)
  obtain ⟨δ,hδ,hδsmall⟩ := exists_rat_btwn hsmall
  have hd1 : (δ:ℝ) < 1/6 := hδsmall.trans_le (min_le_left _ _)
  have hd2 : (δ:ℝ) < (α-1)/12 := hδsmall.trans_le (min_le_right _ _)
  let ρ := (δ:ℝ)*η/(2*c)
  have hcR : (0:ℝ) < c := by exact_mod_cast hc
  have hρ : 0 < ρ := div_pos (mul_pos hδ hη) (by positivity)
  refine ⟨δ,⌈(3/2:ℝ)/ρ⌉₊,⌈6*(α+η)*c/((δ:ℝ)*η)⌉₊,hδ,hd1.le,?_,?_,Nat.le_ceil _⟩
  · linarith
  · exact (div_le_iff₀ hρ).mp (Nat.le_ceil _)

end MetricKMedian.Reduction
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseGraphReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseGraph
open Finset
variable {n m : ℕ}

@[simp] theorem cast_edge (G : Graph n m) (h : Fin n) (i : Fin m) :
    (edge G h i:ℝ)=GraphLaw.edge G h i := by
  by_cases he : h∈G i <;> simp [edge,GraphLaw.edge,he]

end MetricKMedian.SparseGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MetricKMedian
open Preparation Finset

theorem exists_internal_program (ε : ℝ) (hε : 0<ε) :
    ∃ algorithm : Instance → List Bool,
      Nonempty (Binary.PolyProgram InstanceProgram.encode id algorithm) ∧
      ∀ I, Correct ε I (algorithm I) := by
  obtain ⟨s,r,hs,hs1,hr,hα,hfactor⟩ := exists_approximation_slack ε hε
  obtain ⟨p⟩ := exists_rational_all_parameters_s35 hs hs
  obtain ⟨C,hC⟩ := exists_nat_gt (max (0:ℝ) (1+3*(p.round.g:ℝ)+(p.round.allowance:ℝ)))
  have hCap : 1+3*(p.round.g:ℝ)+(p.round.allowance:ℝ)≤(C:ℝ) := (le_max_right _ _).trans hC.le
  have hCp : 0<C := by exact_mod_cast lt_of_le_of_lt (le_max_left _ _) hC
  let α := ((1+2/Real.exp 1+s)/(1-s))*(1+s)*(1+3/(r:ℝ))
  have hPseudo : ∀ I : Instance, I.computedPseudo r hr p C⊆I.facilities ∧ (I.computedPseudo r hr p C).Nonempty ∧
      (I.computedPseudo r hr p C).card≤I.k+C ∧ cost I (I.computedPseudo r hr p C)≤α*optimum I :=
    fun I => I.computedPseudo_spec_s35 r hr p hs.le hs hs1 C hCap
  obtain ⟨δ,a,b,hδ,hsδ,hf,ha,hb⟩ := Reduction.reduction_parameters α (ε/2) hα (by positivity) C hCp
  refine ⟨Reduction.Program.algorithm r hr p C a b δ,
    ⟨(Reduction.Program.ordinaryProgram r hr p C a b δ).comp Binary.BooleanLists.unpackProgram⟩,?_⟩
  intro I
  obtain ⟨hOF,hOn,hOk,hCost⟩ := Reduction.Program.ordinarySet_spec_s35 r hr p C a b δ α (ε/2) hCp hδ hsδ
    (by positivity) hf ha hb hPseudo I
  refine ⟨Reduction.Program.ordinarySet r hr p C a b δ I,hOF,hOn,hOk,rfl,hCost.trans ?_⟩
  exact mul_le_mul_of_nonneg_right hfactor I.optimum_nonneg

theorem exists_binary_program (ε : ℝ) (hε : 0<ε) :
    ∃ algorithm : Instance → List Bool,
      Nonempty (Binary.PolyProgram encodeInstance id algorithm) ∧ ∀ I, Correct ε I (algorithm I) := by
  obtain ⟨algorithm, ⟨P⟩, hP⟩ := exists_internal_program ε hε
  exact ⟨algorithm, ⟨InputParser.instanceProgram.comp P⟩, hP⟩

theorem main_finite_work_oai : ∀ ε : ℝ, 0<ε →
    ∃ (algorithm : Instance → List Bool) (P : Turing.TM2ComputableInPolyTime encodeInstance id algorithm),
      (∀ k : P.tm.K, Finite (P.tm.Γ k)) ∧ ∀ I, Correct ε I (algorithm I) := by
  intro ε hε
  obtain ⟨algorithm,⟨P⟩,hP⟩ := exists_binary_program ε hε
  exact ⟨algorithm,P.stock,P.finite_work,hP⟩

end MetricKMedian
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.main_finite_work_oai := @OAI.MetricKMedian.main_finite_work_oai
