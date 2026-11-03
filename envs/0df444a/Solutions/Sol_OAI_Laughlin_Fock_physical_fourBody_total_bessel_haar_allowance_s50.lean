-- Prove2me | solution 1 for OAI.Laughlin.Fock.physical_fourBody_total_bessel_haar_allowance_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T18:23:06.178402+00:00
-- url     : https://prove2.me/submissions/155a72b4-b887-4381-9cd8-958071bbbd91

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L014
import Definitions.Def_OAIQ050L016
import Theorems.Thm_OAI_Laughlin_Fock_annihilate_coordinate_s50
import Theorems.Thm_OAI_Laughlin_Fock_linearMap_rotation_norm_integrable_s50
import Theorems.Thm_OAI_Laughlin_Fock_physical_pair_norm_haar_real_s50
import Theorems.Thm_OAI_Laughlin_Spin_source_fourBody_local_orthonormal_s50

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

theorem two_annihilate_normSq_le (Q : ℕ) (j k : Fin (Q+1)) (x : Space Q) :
    occupationNormSq Q (annihilate k (annihilate j x)) ≤ occupationNormSq Q x :=
  (annihilate_normSq_le Q k _).trans (annihilate_normSq_le Q j x)

theorem sourceFour_normSq_le_pair (Q p : ℕ) (j k : Fin (Q+1)) (x : Space Q) :
    occupationNormSq Q (sourceFourEnd Q p j k x) ≤
      occupationNormSq Q (sourcePairEnd Q p x) :=
  two_annihilate_normSq_le Q j k (sourcePairEnd Q p x)

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Operators_LocalFourCardinality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators

theorem localFourIndex_card_sum (D : ℕ) :
    Fintype.card (LocalFourIndex D) = ∑ n : Fin (D+1), (n.val+1)/2 := by
  rw [Fintype.card_congr (localFourCountEquiv D),Fintype.card_sigma]
  simp only [Fintype.card_fin]

theorem localFourIndex_card_retained (D : ℕ) (hD : D ≤ 23) :
    Fintype.card (LocalFourIndex D) = (D+1)^2/4 := by
  rw [localFourIndex_card_sum]
  interval_cases D <;> norm_num [Fin.sum_univ_succ]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Operators_OrthonormalRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin
open scoped BigOperators

theorem orthonormal_rows_complex_bound {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] (c : I → J → ℝ) (v : J → ℂ)
    (hc : ∀ i k, (∑ j, c i j * c k j) = if i = k then 1 else 0) :
    (∑ i, ‖∑ j, (c i j : ℂ) * v j‖^2) ≤ ∑ j, ‖v j‖^2 := by
  let u : I → EuclideanSpace ℂ J := fun i => WithLp.toLp 2 (fun j => (c i j : ℂ))
  have hu : Orthonormal ℂ u := by
    rw [orthonormal_iff_ite]
    intro i k
    simp only [u,PiLp.inner_apply,RCLike.inner_apply,
      Complex.conj_ofReal]
    have h := congrArg Complex.ofReal (hc k i)
    simpa only [Complex.ofReal_sum,Complex.ofReal_mul,
      apply_ite,Complex.ofReal_one,Complex.ofReal_zero,eq_comm] using h
  have h := hu.sum_inner_products_le (WithLp.toLp 2 v) (s := Finset.univ)
  simpa only [u,PiLp.inner_apply,PiLp.toLp_apply,RCLike.inner_apply,
    Complex.star_def,Complex.conj_ofReal,EuclideanSpace.norm_sq_eq,mul_comm] using h

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_BesselAllowance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Spin Rotation MeasureTheory
open scoped BigOperators

theorem orthonormal_occupation_sum_bound {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] (Q : ℕ) (c : I → J → ℝ) (v : J → Space Q)
    (hc : ∀ i k, (∑ j, c i j * c k j) = if i = k then 1 else 0) :
    (∑ i, occupationNormSq Q (∑ j, (c i j : ℂ) • v j)) ≤
      ∑ j, occupationNormSq Q (v j) := by
  unfold occupationNormSq
  simp only [map_sum,Finsupp.finsetSum_apply,map_smul,Finsupp.smul_apply,smul_eq_mul]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro A hA
  exact orthonormal_rows_complex_bound c (fun j => (occupationBasis Q).repr (v j) A) hc

end Laughlin.Fock

namespace Laughlin.Fock
open Spin Rotation MeasureTheory
open scoped BigOperators

theorem source_fourBody_bessel_allowance (Q D : ℕ) (hQ : D+2 ≤ Q) (x : Space Q) :
    (∑ r : OddPairLabel D, occupationNormSq Q
      (physicalFourCopyEnd Q (oddPairDeficit r) D (by have := oddPairDeficit_le r; omega) x)) ≤
      ∑ b : LocalFourIndex D, occupationNormSq Q (sourcePairEnd Q b.val.1.val x) := by
  simp only [physicalFourCopyEnd,LinearMap.sum_apply,LinearMap.smul_apply]
  apply (orthonormal_occupation_sum_bound Q
    (fun r : OddPairLabel D => fun b : LocalFourIndex D =>
      fourBodyCoefficient Q (oddPairDeficit r) D D b.val.1.val b.val.2.1.val b.val.2.2.val)
    (fun b => sourceFourEnd Q b.val.1.val ⟨b.val.2.1.val,by omega⟩ ⟨b.val.2.2.val,by omega⟩ x)
    (source_fourBody_local_orthonormal_s50 Q D hQ)).trans
  exact Finset.sum_le_sum (fun b hb => sourceFour_normSq_le_pair Q b.val.1.val _ _ x)

theorem physical_fourBody_bessel_haar_allowance (Q D : ℕ) (hQ : D+2 ≤ Q)
    (x : Space Q) :
    (∑ r : OddPairLabel D, (2*Q-2+1 : ℕ) * (∫ g, occupationNormSq Q
      (physicalFourCopyEnd Q (oddPairDeficit r) D
        (by have := oddPairDeficit_le r; omega) (exteriorRotation Q g⁻¹ x)) ∂sourceHaar)) ≤
      (Fintype.card (LocalFourIndex D) : ℝ) * sourceFockEnergy Q x := by
  have hL (r : OddPairLabel D) : Integrable
      (fun g => occupationNormSq Q (physicalFourCopyEnd Q (oddPairDeficit r) D
        (by have := oddPairDeficit_le r; omega) (exteriorRotation Q g⁻¹ x))) sourceHaar :=
    linearMap_rotation_norm_integrable_s50 Q _ x
  have hP (b : LocalFourIndex D) : Integrable
      (fun g => occupationNormSq Q (sourcePairEnd Q b.val.1.val
        (exteriorRotation Q g⁻¹ x))) sourceHaar :=
    linearMap_rotation_norm_integrable_s50 Q _ x
  have hi := integral_mono
    (integrable_finsetSum _ (fun (r : OddPairLabel D) hr => hL r))
    (integrable_finsetSum _ (fun (b : LocalFourIndex D) hb => hP b))
    (fun g => source_fourBody_bessel_allowance Q D hQ (exteriorRotation Q g⁻¹ x))
  rw [integral_finsetSum _ (fun (r : OddPairLabel D) hr => hL r)] at hi
  rw [← Finset.mul_sum]
  apply (mul_le_mul_of_nonneg_left hi (by positivity : (0 : ℝ) ≤ (2*Q-2+1 : ℕ))).trans_eq
  rw [integral_finsetSum _ (fun (b : LocalFourIndex D) hb => hP b)]
  have hp (b : LocalFourIndex D) :
      (∫ g, occupationNormSq Q (sourcePairEnd Q b.val.1.val (exteriorRotation Q g⁻¹ x))
        ∂sourceHaar) = sourceFockEnergy Q x/(2*Q-2+1 : ℕ) :=
    physical_pair_norm_haar_real_s50 Q (by omega) ⟨b.val.1.val,by have := b.val.1.isLt; omega⟩ x
  simp_rw [hp]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hd : ((2*Q-2+1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

theorem source_bessel_allowance_count_fin :
    (∑ d : Fin 23, (d.val+2)^2/4) = 1222 := by decide +kernel

theorem physical_fourBody_total_bessel_haar_allowance_s50_oai (Q : ℕ) (hQ : 25 ≤ Q)
    (x : Space Q) :
    (∑ d : Fin 23, ∑ r : OddPairLabel (d.val+1),
      (2*Q-2+1 : ℕ) * (∫ g, occupationNormSq Q
        (physicalFourCopyEnd Q (oddPairDeficit r) (d.val+1)
          (by have := oddPairDeficit_le r; omega) (exteriorRotation Q g⁻¹ x)) ∂sourceHaar)) ≤
      1222 * sourceFockEnergy Q x := by
  calc
    _ ≤ ∑ d : Fin 23, ((d.val+2)^2/4 : ℕ) * sourceFockEnergy Q x := by
      apply Finset.sum_le_sum
      intro d hd
      simpa only [localFourIndex_card_retained (d.val+1) (by omega),Nat.add_assoc] using
        physical_fourBody_bessel_haar_allowance Q (d.val+1) (by omega) x
    _ = _ := by
      rw [← Finset.sum_mul,← Nat.cast_sum,source_bessel_allowance_count_fin,Nat.cast_ofNat]

end Laughlin.Fock

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Fock.physical_fourBody_total_bessel_haar_allowance_s50_oai := @OAI.Laughlin.Fock.physical_fourBody_total_bessel_haar_allowance_s50_oai
