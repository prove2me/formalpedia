-- Prove2me | solution 1 for OAI.Laughlin.Spin.source_fourBody_coefficient_tendsto_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T18:58:46.413135+00:00
-- url     : https://prove2.me/submissions/5e31dc4c-1a18-4cab-958e-e726fa17228f

import Mathlib
import Definitions.Def_OAIQ050L022
import Theorems.Thm_OAI_Laughlin_Spin_source_coupling_polynomial_tendsto_s50

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_Array
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem couplingArray_physical (A B z n : ℕ) (hA : z ≤ A) (hB : z ≤ B)
    (hTA : z+n ≤ A) (hTB : z+n ≤ B) (i : SpinIndex A B) (hi : i.1.val+i.2.val=z+n) :
    (-1 : ℝ)^z * genericUnitDescendant A B z hA hB n i = couplingArray A B z n i.1.val := by
  induction n generalizing i with
  | zero =>
    rw [genericUnitDescendant_zero]
    let p : Fin (z+1) := ⟨i.1.val,by omega⟩
    have he : i = weightSliceIndex A B z hA hB p := by
      apply Prod.ext
      · rfl
      · apply Fin.ext; dsimp [weightSliceIndex,p]; omega
    rw [he]
    change (-1 : ℝ)^z * extendWeightSlice A B z hA hB (fun q => highestUnit A B z q.val)
      (weightSliceIndex A B z hA hB p) = (-1 : ℝ)^z * highestUnit A B z p.val
    rw [extendWeightSlice_at]
  | succ n ih =>
    have hn : n < genericCoupledWeight A B z := by unfold genericCoupledWeight; omega
    have hnreal : (n : ℝ) < genericCoupledWeight A B z := by exact_mod_cast hn
    have hd : Real.sqrt (((n : ℝ)+1)*((genericCoupledWeight A B z : ℝ)-n)) ≠ 0 := by positivity
    have he := congrFun (genericUnitDescendant_lowering A B z n hA hB hn) i
    change (∑ j, totalRaise A B j i * genericUnitDescendant A B z hA hB n j) =
      Real.sqrt (((n : ℝ)+1)*((genericCoupledWeight A B z : ℝ)-n))*
        genericUnitDescendant A B z hA hB (n+1) i at he
    rw [totalRaise_transpose_apply,raiseMatrix_column,raiseMatrix_column] at he
    have h1 : (-1 : ℝ)^z *
        (if h : 0 < i.1.val then genericUnitDescendant A B z hA hB n (⟨i.1.val-1,by omega⟩,i.2) *
          ladder A (i.1.val-1) else 0) =
        (if i.1.val=0 then 0 else ladder A (i.1.val-1)*couplingArray A B z n (i.1.val-1)) := by
      by_cases hp : 0 < i.1.val
      · rw [dite_eq_left hp,ite_eq_right (by omega : i.1.val ≠ 0)]
        have hh := ih (by omega) (by omega) (⟨i.1.val-1,by omega⟩,i.2) (by dsimp; omega)
        dsimp at hh
        rw [← hh]; ring
      · rw [dite_eq_right hp,ite_eq_left (by omega : i.1.val=0),mul_zero]
    have h2 : (-1 : ℝ)^z *
        (if h : 0 < i.2.val then genericUnitDescendant A B z hA hB n (i.1,⟨i.2.val-1,by omega⟩) *
          ladder B (i.2.val-1) else 0) =
        (if i.1.val ≤ z+n then ladder B (z+n-i.1.val)*couplingArray A B z n i.1.val else 0) := by
      by_cases hp : 0 < i.2.val
      · rw [dite_eq_left hp,ite_eq_left (by omega : i.1.val ≤ z+n)]
        have hh := ih (by omega) (by omega) (i.1,⟨i.2.val-1,by omega⟩) (by dsimp; omega)
        dsimp at hh
        have hl : ladder B (i.2.val-1) = ladder B (z+n-i.1.val) := congrArg (ladder B) (by omega)
        rw [← hh,hl]; ring
      · rw [dite_eq_right hp,ite_eq_right (by omega : ¬ i.1.val ≤ z+n),mul_zero]
    change _ = (_ + _) / _
    apply (eq_div_iff hd).mpr
    linear_combination h1+h2-(-1 : ℝ)^z*he

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Operators_PhysicalCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped Topology
open Filter

theorem physicalCouplingCoefficient_eq_array (A B z T p : ℕ)
    (hz : z ≤ T) (hp : p ≤ T) (hA : T ≤ A) (hB : T ≤ B) :
    physicalCouplingCoefficient A B z T p = couplingArray A B z (T-z) p := by
  rw [physicalCouplingCoefficient,dite_eq_left ⟨hz,hp,hA,hB⟩]
  exact couplingArray_physical A B z (T-z) (by omega) (by omega) (by omega) (by omega)
    (⟨p,by omega⟩,⟨T-p,by omega⟩) (by dsimp; omega)

theorem source_physical_coupling_tendsto (A B : ℕ → ℕ) (b : ℝ)
    (hA : Tendsto A atTop atTop) (hB : Tendsto B atTop atTop)
    (hb0 : 0 < b) (hb1 : b < 1)
    (hfrac : Tendsto (fun j => (B j : ℝ)/((A j : ℝ)+B j)) atTop (𝓝 b))
    (z T p : ℕ) (hz : z ≤ T) (hp : p ≤ T) :
    Tendsto (fun j => physicalCouplingCoefficient (A j) (B j) z T p) atTop
      (𝓝 (couplingPolynomialCoefficient (Real.sqrt b) (Real.sqrt (1-b)) z (T-z) p)) := by
  apply (source_coupling_polynomial_tendsto_s50 A B b hA hB hb0 hb1 hfrac z T p hz hp).congr'
  filter_upwards [hA.eventually (eventually_ge_atTop T),hB.eventually (eventually_ge_atTop T)] with j hjA hjB
  exact (physicalCouplingCoefficient_eq_array (A j) (B j) z T p hz hp hjA hjB).symm

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_Specializations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped Topology
open Filter

theorem affine_spin_tendsto (a c : ℕ) (ha : 0 < a) :
    Tendsto (fun Q : ℕ => a*Q-c) atTop atTop := by
  apply tendsto_atTop.mpr
  intro k
  filter_upwards [eventually_ge_atTop (k+c)] with Q hQ
  have hm : Q ≤ a*Q := by
    simpa using Nat.mul_le_mul_right Q (show 1 ≤ a by omega)
  omega

theorem affine_spin_fraction_tendsto (a b c d : ℕ) (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun Q : ℕ => ((b*Q-d : ℕ) : ℝ)/(((a*Q-c : ℕ) : ℝ)+((b*Q-d : ℕ) : ℝ)))
      atTop (𝓝 ((b : ℝ)/((a : ℝ)+b))) := by
  have har : (0 : ℝ) < a := by exact_mod_cast ha
  have hbr : (0 : ℝ) < b := by exact_mod_cast hb
  have ht : Tendsto (fun Q : ℕ => (-(d : ℝ)+(b : ℝ)*Q)/
      (-(c : ℝ)-(d : ℝ)+((a : ℝ)+b)*Q)) atTop (𝓝 ((b : ℝ)/((a : ℝ)+b))) :=
    tendsto_add_mul_div_add_mul_atTop_nhds (-(d : ℝ)) (-(c : ℝ)-(d : ℝ)) (b : ℝ) (by positivity)
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (c+d)] with Q hQ
  have hmA : Q ≤ a*Q := by simpa using Nat.mul_le_mul_right Q (show 1 ≤ a by omega)
  have hmB : Q ≤ b*Q := by simpa using Nat.mul_le_mul_right Q (show 1 ≤ b by omega)
  rw [Nat.cast_sub (by omega : c ≤ a*Q),Nat.cast_sub (by omega : d ≤ b*Q)]
  push_cast
  congr 1 <;> ring

theorem source_fourBody_inner_coupling_tendsto (r T p : ℕ) (hr : r ≤ T) (hp : p ≤ T) :
    Tendsto (fun Q : ℕ => physicalCouplingCoefficient Q Q r T p) atTop
      (𝓝 (couplingPolynomialCoefficient (Real.sqrt (1/2)) (Real.sqrt (1/2)) r (T-r) p)) := by
  have hf : Tendsto (fun Q : ℕ => (Q : ℝ)/((Q : ℝ)+Q)) atTop (𝓝 (1/2 : ℝ)) := by
    have h := affine_spin_fraction_tendsto 1 1 0 0 (by omega) (by omega)
    norm_num at h ⊢
    exact h
  have hh := source_physical_coupling_tendsto (fun Q => Q) (fun Q => Q) (1/2) tendsto_id tendsto_id
    (by norm_num) (by norm_num) hf r T p hr hp
  norm_num at hh ⊢
  exact hh

theorem source_fourBody_outer_coupling_tendsto (r z T p : ℕ) (hz : z ≤ T) (hp : p ≤ T) :
    Tendsto (fun Q : ℕ => physicalCouplingCoefficient (2*Q-2) (2*Q-2*r) z T p) atTop
      (𝓝 (couplingPolynomialCoefficient (Real.sqrt (1/2)) (Real.sqrt (1/2)) z (T-z) p)) := by
  have hf : Tendsto (fun Q : ℕ => ((2*Q-2*r : ℕ) : ℝ)/
      (((2*Q-2 : ℕ) : ℝ)+((2*Q-2*r : ℕ) : ℝ))) atTop (𝓝 (1/2 : ℝ)) := by
    have h := affine_spin_fraction_tendsto 2 2 2 (2*r) (by omega) (by omega)
    norm_num at h ⊢
    exact h
  have hh := source_physical_coupling_tendsto (fun Q => 2*Q-2) (fun Q => 2*Q-2*r) (1/2)
    (affine_spin_tendsto 2 2 (by omega)) (affine_spin_tendsto 2 (2*r) (by omega))
    (by norm_num) (by norm_num) hf z T p hz hp
  norm_num at hh ⊢
  exact hh

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_CoefficientLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped Topology
open Filter

theorem source_fourBody_coefficient_tendsto_s50_oai (r D T p j k : ℕ)
    (hrD : r ≤ D) (hDT : D ≤ T) (hT : p+j+k=T) :
    Tendsto (fun Q : ℕ => fourBodyCoefficient Q r D T p j k) atTop
      (𝓝 (fourBodyLimitCoefficient r D T p j k)) := by
  by_cases hr : r ≤ j+k
  · simp only [fourBodyCoefficient,fourBodyLimitCoefficient,ite_eq_left hr]
    have hI := source_fourBody_inner_coupling_tendsto r (j+k) j hr (by omega)
    have hO := source_fourBody_outer_coupling_tendsto r (D-r) (T-r) p (by omega) (by omega)
    have he : T-r-(D-r)=T-D := by omega
    rw [he] at hO
    exact (tendsto_const_nhds.mul hI).mul hO
  · simp only [fourBodyCoefficient,fourBodyLimitCoefficient,ite_eq_right hr]
    exact tendsto_const_nhds

end Laughlin.Spin

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Spin.source_fourBody_coefficient_tendsto_s50_oai := @OAI.Laughlin.Spin.source_fourBody_coefficient_tendsto_s50_oai
