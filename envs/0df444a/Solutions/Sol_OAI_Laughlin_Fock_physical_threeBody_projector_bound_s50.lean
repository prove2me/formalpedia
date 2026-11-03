-- Prove2me | solution 1 for OAI.Laughlin.Fock.physical_threeBody_projector_bound_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T18:25:42.044474+00:00
-- url     : https://prove2.me/submissions/dc6b1fae-e313-4152-b514-3af0f7e9866b

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L014
import Definitions.Def_OAIQ050L016
import Definitions.Def_OAIQ050L017
import Theorems.Thm_OAI_Laughlin_Fock_annihilate_coordinate_s50
import Theorems.Thm_OAI_Laughlin_Fock_linearMap_rotation_norm_integrable_s50
import Theorems.Thm_OAI_Laughlin_Fock_physical_pair_norm_haar_real_s50
import Theorems.Thm_OAI_Laughlin_Fock_sourceThreeHighestEnd_haar_s50

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Fock_Annihilation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock

theorem insertionSign_spec (Q : ℕ) (i : Fin (Q+1)) (A : Finset (Fin (Q+1))) :
    insertionSign Q i A = 1 ∨ insertionSign Q i A = -1 := by
  by_cases h : i ∉ A
  · simpa [insertionSign,h] using (create_unoccupied_sign Q i A h).choose_spec.1
  · simp [insertionSign,h]

theorem insertionSign_norm (Q : ℕ) (i : Fin (Q+1)) (A : Finset (Fin (Q+1))) :
    ‖insertionSign Q i A‖ = 1 := by
  rcases insertionSign_spec Q i A with h | h <;> simp [h]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Fock_ContractionBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem sum_unoccupied_insert {Q : ℕ} {R : Type*} [AddCommMonoid R]
    (i : Fin (Q+1)) (f : Finset (Fin (Q+1)) → R) :
    (∑ A ∈ Finset.univ.filter (fun A : Finset (Fin (Q+1)) => i ∉ A), f (insert i A)) =
      ∑ A ∈ Finset.univ.filter (fun A : Finset (Fin (Q+1)) => i ∈ A), f A := by
  classical
  apply Finset.sum_bij (fun A _ => insert i A)
  · intro A hA
    simp
  · intro A hA B hB h
    have ha := (Finset.mem_filter.mp hA).2
    have hb := (Finset.mem_filter.mp hB).2
    have he := congrArg (fun C => C.erase i) h
    simpa [Finset.erase_insert,ha,hb] using he
  · intro B hB
    have hb := (Finset.mem_filter.mp hB).2
    exact ⟨B.erase i,by simp,Finset.insert_erase hb⟩
  · intro A hA
    rfl

theorem annihilate_normSq (Q : ℕ) (i : Fin (Q+1)) (x : Space Q) :
    occupationNormSq Q (annihilate i x) =
      ∑ A : Finset (Fin (Q+1)), if i ∈ A then ‖(occupationBasis Q).repr x A‖^2 else 0 := by
  have h (A : Finset (Fin (Q+1))) :
      ‖(occupationBasis Q).repr (annihilate i x) A‖^2 =
        if i ∉ A then ‖(occupationBasis Q).repr x (insert i A)‖^2 else 0 := by
    by_cases hi : i ∈ A <;> simp [annihilate_coordinate_s50,hi,insertionSign_norm]
  unfold occupationNormSq
  simp_rw [h]
  simpa only [Finset.sum_filter] using
    sum_unoccupied_insert (R := ℝ) i (fun A => ‖(occupationBasis Q).repr x A‖^2)

theorem annihilate_normSq_le (Q : ℕ) (i : Fin (Q+1)) (x : Space Q) :
    occupationNormSq Q (annihilate i x) ≤ occupationNormSq Q x := by
  rw [annihilate_normSq]
  unfold occupationNormSq
  apply Finset.sum_le_sum
  intro A hA
  split_ifs
  · exact le_rfl
  · positivity

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Operators_WeightedOccupationNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem normalized_occupation_sum_bound {I : Type*} [Fintype I] (Q : ℕ)
    (c : I → ℝ) (v : I → Space Q) (hc : (∑ i, (c i)^2)=1) :
    occupationNormSq Q (∑ i, (c i : ℂ) • v i) ≤ ∑ i, occupationNormSq Q (v i) := by
  unfold occupationNormSq
  simp only [map_sum,Finsupp.finsetSum_apply,map_smul,Finsupp.smul_apply,smul_eq_mul]
  rw [Finset.sum_comm (f := fun i A => ‖(occupationBasis Q).repr (v i) A‖^2)]
  apply Finset.sum_le_sum
  intro A hA
  have ht : ‖∑ i, (c i : ℂ) * (occupationBasis Q).repr (v i) A‖ ≤
      ∑ i, |c i| * ‖(occupationBasis Q).repr (v i) A‖ := by
    simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs] using
      (norm_sum_le Finset.univ (fun i => (c i : ℂ) * (occupationBasis Q).repr (v i) A))
  have hs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => |c i|)
    (fun i => ‖(occupationBasis Q).repr (v i) A‖)
  simp only [sq_abs,hc,one_mul] at hs
  exact (pow_le_pow_left₀ (norm_nonneg _) ht 2).trans hs

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_ThreeBody_HighestFock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation Spin MeasureTheory
open scoped BigOperators Matrix

theorem sourceThreeHighestEnd_norm_bound (Q z : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q) (x : Space Q) :
    occupationNormSq Q (sourceThreeHighestEnd Q z hQ hz x) ≤
      ∑ p : Fin (z+1), occupationNormSq Q (sourcePairEnd Q p.val x) := by
  have hn : (∑ p : Fin (z+1), (highestUnit (2*Q-2) Q z p.val)^2)=1 := by
    rw [Fin.sum_univ_eq_sum_range (fun p => (highestUnit (2*Q-2) Q z p)^2) (z+1)]
    exact highestUnit_norm (2*Q-2) Q z (by omega) hz
  simp only [sourceThreeHighestEnd,LinearMap.sum_apply,LinearMap.smul_apply]
  apply (normalized_occupation_sum_bound Q _ _ hn).trans
  apply Finset.sum_le_sum
  intro p hp
  exact annihilate_normSq_le Q _ (sourcePairEnd Q p.val x)

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_ThreeBody_ProjectorBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation Spin MeasureTheory
open scoped BigOperators Matrix

theorem physical_threeBody_projector_bound_s50_oai (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1)) (x : Space Q) :
    (contractionForm Q (sourceThreeEnd Q)
      ((threeSpinProjector Q hQ z).map Complex.ofReal) x).re ≤
      ((coupledWeight Q z.val+1 : ℕ) / (2*Q-2+1 : ℕ) : ℝ) *
        (z.val+1 : ℕ) * sourceFockEnergy Q x := by
  rw [← sourceThreeHighestEnd_haar_s50 Q hQ z]
  have hi := integral_mono
    (linearMap_rotation_norm_integrable_s50 Q (sourceThreeHighestEnd Q z.val hQ (by omega)) x)
    (integrable_finsetSum _ (fun (p : Fin (z.val+1)) hp =>
      linearMap_rotation_norm_integrable_s50 Q (sourcePairEnd Q p.val) x))
    (fun g => sourceThreeHighestEnd_norm_bound Q z.val hQ (by omega) (exteriorRotation Q g⁻¹ x))
  apply (mul_le_mul_of_nonneg_left hi
    (by positivity : (0 : ℝ) ≤ (coupledWeight Q z.val+1 : ℕ))).trans_eq
  rw [integral_finsetSum _ (fun (p : Fin (z.val+1)) hp =>
    linearMap_rotation_norm_integrable_s50 Q (sourcePairEnd Q p.val) x)]
  have hp (p : Fin (z.val+1)) :
      (∫ g, occupationNormSq Q (sourcePairEnd Q p.val (exteriorRotation Q g⁻¹ x)) ∂sourceHaar) =
        sourceFockEnergy Q x/(2*Q-2+1 : ℕ) :=
    physical_pair_norm_haar_real_s50 Q (by omega) ⟨p.val,by have := p.isLt; have := z.isLt; omega⟩ x
  simp_rw [hp]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

end Laughlin.Fock

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Fock.physical_threeBody_projector_bound_s50_oai := @OAI.Laughlin.Fock.physical_threeBody_projector_bound_s50_oai
