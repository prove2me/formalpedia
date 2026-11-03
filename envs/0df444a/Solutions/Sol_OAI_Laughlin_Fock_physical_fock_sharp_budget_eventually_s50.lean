-- Prove2me | solution 1 for OAI.Laughlin.Fock.physical_fock_sharp_budget_eventually_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T18:46:58.067249+00:00
-- url     : https://prove2.me/submissions/53b7c8d1-77fd-4106-8726-e7feaf25a7f6

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L020
import Theorems.Thm_OAI_Laughlin_Fock_complexThreeGram_sub_one_spectral_s50
import Theorems.Thm_OAI_Laughlin_Fock_physical_threeBody_Fock_comparison_eventually_s50
import Theorems.Thm_OAI_Laughlin_Fock_physical_threeBody_projector_bound_s50
import Theorems.Thm_OAI_Laughlin_Fock_physical_threeBody_projector_nonneg_s50
import Theorems.Thm_OAI_Laughlin_Fock_sourceA4Form_bessel_bound_s50
import Theorems.Thm_OAI_Laughlin_Fock_sourceFockHamiltonian_normal_square_s50
import Theorems.Thm_OAI_Laughlin_Fock_sourceKForm_decomposition_s50

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Asymptotics_Bound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin
noncomputable section
open scoped BigOperators

theorem tail_bracket_bounds {Q z : ℕ} (hQ : 4 ≤ Q) (hz₀ : 16 ≤ z) (hz : z ≤ Q) :
    0 ≤ 3*(z : ℝ)-1-(z : ℝ)*((z : ℝ)+1)/(Q : ℝ) ∧
      3*(z : ℝ)-1-(z : ℝ)*((z : ℝ)+1)/(Q : ℝ) ≤ 3*(z : ℝ) := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have hzr : (16 : ℝ) ≤ z := by exact_mod_cast hz₀
  have hzQr : (z : ℝ) ≤ Q := by exact_mod_cast hz
  have hd : (z : ℝ)*((z : ℝ)+1)/(Q : ℝ) ≤ (z : ℝ)+1 := by
    apply (div_le_iff₀ hQr).mpr
    nlinarith
  have hn : 0 ≤ (z : ℝ)*((z : ℝ)+1)/(Q : ℝ) := by positivity
  constructor <;> linarith

end
end Laughlin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Asymptotics_Convergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin
open scoped BigOperators Topology
open Filter
noncomputable section

theorem odd_tail_index_iff (z : ℕ) : (17 ≤ z ∧ Odd z) ↔ ∃ m : ℕ, z = 17+2*m := by
  constructor
  · rintro ⟨hz, k, hk⟩
    exact ⟨k-8, by omega⟩
  · rintro ⟨m, rfl⟩
    exact ⟨by omega, ⟨8+m, by omega⟩⟩

theorem deltaFormula_eq_finite_sum (Q : ℕ) :
    deltaFormula Q = ∑ m ∈ Finset.range (Q+1), deltaTerm Q m := by
  apply tsum_eq_sum
  intro m hm
  have hn : ¬ 17+2*m ≤ Q := by
    simp only [Finset.mem_range] at hm
    omega
  simp [deltaTerm, hn]

end
end Laughlin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Asymptotics_FiniteReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin
open scoped BigOperators

theorem deltaFormula_eq_odd_finite_sum (Q : ℕ) :
    deltaFormula Q = ∑ z ∈ (Finset.range (Q+1)).filter (fun z => 17 ≤ z ∧ Odd z), tailWeight Q z := by
  rw [deltaFormula_eq_finite_sum]
  simp only [deltaTerm]
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun z hz => (z-17)/2)
  · intro z hz
    simp only [Finset.mem_filter,Finset.mem_range] at hz ⊢
    obtain ⟨m,hm⟩ := (odd_tail_index_iff z).mp hz.2
    omega
  · intro z hz w hw he
    simp only [Finset.mem_filter,Finset.mem_range] at hz hw
    obtain ⟨m,hm⟩ := (odd_tail_index_iff z).mp hz.2
    obtain ⟨n,hn⟩ := (odd_tail_index_iff w).mp hw.2
    omega
  · intro m hm
    simp only [Finset.mem_filter,Finset.mem_range] at hm
    refine ⟨17+2*m,?_,by omega⟩
    simp only [Finset.mem_filter,Finset.mem_range]
    exact ⟨by omega,(odd_tail_index_iff _).mpr ⟨m,rfl⟩⟩
  · intro z hz
    simp only [Finset.mem_filter,Finset.mem_range] at hz
    obtain ⟨m,hm⟩ := (odd_tail_index_iff z).mp hz.2
    congr 1
    omega

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Pair_FockHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation MeasureTheory
open scoped BigOperators Matrix

theorem contractionForm_smul {I : Type*} [Fintype I] (Q : ℕ)
    (minus : I → Module.End ℂ (Space Q)) (c : ℂ) (M : Matrix I I ℂ) (x : Space Q) :
    contractionForm Q minus (c • M) x = c * contractionForm Q minus M x := by
  simp only [contractionForm,Matrix.smul_apply,smul_eq_mul,Finset.mul_sum,mul_assoc]

theorem contractionForm_sum {I J : Type*} [Fintype I] [Fintype J] (Q : ℕ)
    (minus : I → Module.End ℂ (Space Q)) (M : J → Matrix I I ℂ) (x : Space Q) :
    contractionForm Q minus (∑ j, M j) x = ∑ j, contractionForm Q minus (M j) x := by
  simp only [contractionForm,Matrix.sum_apply,Finset.sum_mul]
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_ThreeBody_FockTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation Spin MeasureTheory
open scoped BigOperators Matrix

theorem threeBody_dimension_ratio (Q z : ℕ) (hQ : 4 ≤ Q) (hz : z ≤ Q) :
    ((coupledWeight Q z+1 : ℕ)/(2*Q-2+1 : ℕ) : ℝ) =
      (3*(Q : ℝ)-1-2*(z : ℝ))/(2*(Q : ℝ)-1) := by
  have hn : ((coupledWeight Q z+1 : ℕ) : ℝ)=3*(Q : ℝ)-1-2*(z : ℝ) := by
    unfold coupledWeight
    rw [Nat.cast_add,Nat.cast_sub (by omega : 2*z ≤ 3*Q-2),
      Nat.cast_sub (by omega : 2 ≤ 3*Q)]
    push_cast
    ring
  have hd : ((2*Q-2+1 : ℕ) : ℝ)=2*(Q : ℝ)-1 := by
    rw [Nat.cast_add,Nat.cast_sub (by omega : 2 ≤ 2*Q)]
    push_cast
    ring
  rw [hn,hd]

theorem physical_threeBody_tail_sum (Q : ℕ) (hQ : 4 ≤ Q) (x : Space Q) :
    -(deltaFormula Q * sourceFockEnergy Q x) ≤
      ∑ z : Fin (Q+1), if 16 ≤ z.val then gramEigenvalueFormula Q z.val *
        (contractionForm Q (sourceThreeEnd Q)
          ((threeSpinProjector Q (by omega) z).map Complex.ofReal) x).re else 0 := by
  let P := fun z : Fin (Q+1) => (contractionForm Q (sourceThreeEnd Q)
    ((threeSpinProjector Q (by omega) z).map Complex.ofReal) x).re
  have hP (z : Fin (Q+1)) : 0 ≤ P z := physical_threeBody_projector_nonneg_s50 Q (by omega) z x
  have hb (z : Fin (Q+1)) : P z ≤
      ((3*(Q : ℝ)-1-2*(z.val : ℝ))/(2*(Q : ℝ)-1))*
        (z.val+1 : ℕ)*sourceFockEnergy Q x := by
    simpa only [threeBody_dimension_ratio Q z.val hQ (by omega)] using
      physical_threeBody_projector_bound_s50 Q (by omega) z x
  have ht (z : Fin (Q+1)) :
      -(if 17 ≤ z.val ∧ Odd z.val then tailWeight Q z.val else 0) * sourceFockEnergy Q x ≤
        if 16 ≤ z.val then gramEigenvalueFormula Q z.val * P z else 0 := by
    by_cases hz : 16 ≤ z.val
    · rw [ite_eq_left hz]
      by_cases ho : Odd z.val
      · have hz17 : 17 ≤ z.val := by obtain ⟨k,hk⟩ := ho; omega
        rw [ite_eq_left ⟨hz17,ho⟩]
        have h₁ := mul_le_mul_of_nonneg_left (hb z) (abs_nonneg (gramEigenvalueFormula Q z.val))
        have h₂ := mul_le_mul_of_nonneg_right (neg_abs_le (gramEigenvalueFormula Q z.val)) (hP z)
        unfold tailWeight
        push_cast at h₁ ⊢
        nlinarith
      · rw [ite_eq_right (by tauto)]
        have he : Even z.val := Nat.not_odd_iff_even.mp ho
        have hpow : (-1 : ℝ)^z.val=1 := he.neg_one_pow
        have hg : 0 ≤ gramEigenvalueFormula Q z.val := by
          unfold gramEigenvalueFormula
          rw [hpow,one_mul]
          exact mul_nonneg (by unfold fallingRatio; positivity) (tail_bracket_bounds hQ hz (by omega)).1
        simpa using mul_nonneg hg (hP z)
    · have hn : ¬ (17 ≤ z.val ∧ Odd z.val) := by omega
      simp only [ite_eq_right hz,ite_eq_right hn,neg_zero,zero_mul,le_refl]
  have hs : (∑ z : Fin (Q+1), if 17 ≤ z.val ∧ Odd z.val then tailWeight Q z.val else 0)=deltaFormula Q := by
    rw [Fin.sum_univ_eq_sum_range (fun z => if 17 ≤ z ∧ Odd z then tailWeight Q z else 0) (Q+1),
      ← Finset.sum_filter,← deltaFormula_eq_odd_finite_sum]
  have h := Finset.sum_le_sum (s := Finset.univ) (fun z hz => ht z)
  simpa only [← Finset.sum_mul,Finset.sum_neg_distrib,hs,neg_mul] using h

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_ThreeBody_FockBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation Spin MeasureTheory Filter
open scoped BigOperators Matrix

theorem physical_threeBody_budget_eventually :
    ∀ᶠ Q : ℕ in atTop, ∃ _ : 15 ≤ Q, ∀ x : Space Q,
      (2*Q-2+1 : ℕ) * (∫ g, contractionForm Q (sourceThreeEnd Q)
        ((physicalThreeBodyMatrix Q).map Complex.ofReal) (exteriorRotation Q g⁻¹ x) ∂sourceHaar).re -
          deltaFormula Q * sourceFockEnergy Q x ≤
      (contractionForm Q (sourceThreeEnd Q) (complexThreeGram Q-1) x).re := by
  filter_upwards [physical_threeBody_Fock_comparison_eventually_s50] with Q h
  obtain ⟨hQ,h⟩ := h
  refine ⟨hQ,fun x => ?_⟩
  have hlo := h x
  have htail := physical_threeBody_tail_sum Q (by omega) x
  rw [complexThreeGram_sub_one_spectral_s50 Q (by omega),contractionForm_sum,Complex.re_sum]
  simp only [contractionForm_smul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  let f := fun z : Fin (Q+1) => gramEigenvalueFormula Q z.val *
    (contractionForm Q (sourceThreeEnd Q) ((threeSpinProjector Q (by omega) z).map Complex.ofReal) x).re
  have he : (∑ z, f z) = (∑ z, if z.val ≤ 15 then f z else 0) +
      (∑ z, if 16 ≤ z.val then f z else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro z hz
    by_cases h15 : z.val ≤ 15
    · simp [h15,show ¬16 ≤ z.val by omega]
    · simp [h15,show 16 ≤ z.val by omega]
  change _ ≤ ∑ z, f z
  rw [he]
  change _ ≤ ∑ z, if z.val ≤ 15 then f z else 0 at hlo
  change _ ≤ ∑ z, if 16 ≤ z.val then f z else 0 at htail
  linarith

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Fock_SharpGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin
open Filter
open scoped Topology BigOperators

namespace Fock

theorem physical_fock_sharp_budget_eventually_s50_oai :
    ∀ᶠ Q : ℕ in atTop, ∃ hQ : 25 ≤ Q, ∀ x : Space Q,
      sourceKForm Q (by omega) x +
        (1-93527408868499/10^14-deltaFormula Q-1222*(3/10^6)-averagedFourTransferError Q) *
          sourceFockEnergy Q x ≤ occupationNormSq Q (sourceFockHamiltonian Q x) := by
  filter_upwards [physical_threeBody_budget_eventually,eventually_ge_atTop 25] with Q h3 h25
  obtain ⟨h15,h3⟩ := h3
  refine ⟨h25,fun x => ?_⟩
  have h3x := h3 x
  change sourceA3Form Q x-deltaFormula Q*sourceFockEnergy Q x ≤ _ at h3x
  have h4 := sourceA4Form_bessel_bound_s50 Q h25 x
  have hs := sourceFockHamiltonian_normal_square_s50 Q (by omega) x
  rw [sourceKForm_decomposition_s50 Q h25]
  nlinarith

end Fock
end Laughlin

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Fock.physical_fock_sharp_budget_eventually_s50_oai := @OAI.Laughlin.Fock.physical_fock_sharp_budget_eventually_s50_oai
