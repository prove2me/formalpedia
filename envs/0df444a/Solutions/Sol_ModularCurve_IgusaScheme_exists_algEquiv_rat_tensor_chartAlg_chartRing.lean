-- Prove2me | solution 1 for ModularCurve.IgusaScheme.exists_algEquiv_rat_tensor_chartAlg_chartRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/8d33f8d3-15cb-5e20-bc0d-7f1169f63697

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_JacJ1_ChartAlgebra
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IgusaScheme_exists_algEquiv_rat_tensor_chartAlg_chartRing

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false

noncomputable section

p2m_open "ModularCurve P2MW.S_ModularCurve_IgusaScheme_exists_algEquiv_rat_tensor_chartAlg_chartRing.ModularCurve ModularCurve.IgusaScheme P2MW.S_ModularCurve_IgusaScheme_exists_algEquiv_rat_tensor_chartAlg_chartRing.ModularCurve.IgusaScheme"

namespace ModularCurve
p2m_export "ModularCurve" "IgusaScheme modularFunctionFieldFull"
p2m_open "ModularCurve"
namespace IgusaScheme
p2m_export "ModularCurve.IgusaScheme" "chartAlg mem_chartAlg_iff"
p2m_open "ModularCurve.IgusaScheme"

open Polynomial
open scoped TensorProduct

variable (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]

set_option quotPrecheck false in
local notation "ℤℓ" => ↥(GaloisRep.ratLocalizedAt ℓ)
set_option quotPrecheck false in
local notation "FN" => ↥(modularFunctionFieldFull N)

theorem exists_nat_mul_mem_adjoin (S : Set FN) {c : FN} (hc : c ∈ Algebra.adjoin ℚ S) :
    ∃ n : ℕ, n ≠ 0 ∧ (n : FN) * c ∈ Algebra.adjoin ℤℓ S := by
  induction hc using Algebra.adjoin_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by rw [Nat.cast_one, one_mul]; exact Algebra.subset_adjoin hy⟩
  | algebraMap q =>
    refine ⟨q.den, q.den_nz, ?_⟩
    have : (q.den : FN) * algebraMap ℚ FN q = ((q.num : ℤ) : FN) := by
      rw [← map_natCast (algebraMap ℚ FN), ← map_mul, mul_comm, Rat.mul_den_eq_num, map_intCast]
    rw [this]
    exact Subalgebra.intCast_mem _ _
  | add y z _ _ hy hz =>
    obtain ⟨m, hm0, hm⟩ := hy
    obtain ⟨n, hn0, hn⟩ := hz
    refine ⟨m * n, mul_ne_zero hm0 hn0, ?_⟩
    have : ((m * n : ℕ) : FN) * (y + z) = (n : FN) * ((m : FN) * y) + (m : FN) * ((n : FN) * z) := by
      push_cast; ring
    rw [this]
    exact add_mem (Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ _) hm)
      (Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ _) hn)
  | mul y z _ _ hy hz =>
    obtain ⟨m, hm0, hm⟩ := hy
    obtain ⟨n, hn0, hn⟩ := hz
    refine ⟨m * n, mul_ne_zero hm0 hn0, ?_⟩
    have : ((m * n : ℕ) : FN) * (y * z) = ((m : FN) * y) * ((n : FN) * z) := by
      push_cast; ring
    rw [this]
    exact Subalgebra.mul_mem _ hm hn

theorem adjoin_ratLocalizedAt_le_adjoin_rat (S : Set FN) :
    (Algebra.adjoin ℤℓ S).toSubring ≤ (Algebra.adjoin ℚ S).toSubring := by
  intro x hx
  change x ∈ Algebra.adjoin ℤℓ S at hx
  change x ∈ Algebra.adjoin ℚ S
  induction hx using Algebra.adjoin_induction with
  | mem y hy => exact Algebra.subset_adjoin hy
  | algebraMap a =>
    have : algebraMap ℤℓ FN a = algebraMap ℚ FN (a : ℚ) := rfl
    rw [this]
    exact Subalgebra.algebraMap_mem _ _
  | add y z _ _ hy hz => exact add_mem hy hz
  | mul y z _ _ hy hz => exact mul_mem hy hz

theorem chartAlg_le_chartRing (S : Set FN) {x : FN} (hx : x ∈ chartAlg N ℓ S) :
    x ∈ AlgebraicCurve.CurveModel.chartRing ℚ S := by
  rw [AlgebraicCurve.CurveModel.mem_chartRing_iff]
  rw [mem_chartAlg_iff] at hx
  let f : Algebra.adjoin ℤℓ S →+* Algebra.adjoin ℚ S :=
    (Subring.inclusion (adjoin_ratLocalizedAt_le_adjoin_rat N ℓ S))
  exact hx.map_of_comp_eq f (RingHom.id FN) (by ext; rfl)

theorem exists_nat_mul_mem_chartAlg (S : Set FN) {x : FN}
    (hx : x ∈ AlgebraicCurve.CurveModel.chartRing ℚ S) :
    ∃ n : ℕ, n ≠ 0 ∧ (n : FN) * x ∈ chartAlg N ℓ S := by
  classical
  obtain ⟨p, hmonic, hroot⟩ := (AlgebraicCurve.CurveModel.mem_chartRing_iff ℚ).mp hx
  have hcoeff : ∀ i, ∃ n : ℕ, n ≠ 0 ∧ (n : FN) * (p.coeff i : FN) ∈ Algebra.adjoin ℤℓ S :=
    fun i => exists_nat_mul_mem_adjoin N ℓ S (p.coeff i).2
  choose n hn0 hn using hcoeff
  set M : ℕ := ∏ i ∈ Finset.range (p.natDegree + 1), n i with hM
  have hM0 : M ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hn0 i
  have hdvd : ∀ i ≤ p.natDegree, n i ∣ M := fun i hi =>
    Finset.dvd_prod_of_mem n (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  set q : FN[X] := (p.map (algebraMap (Algebra.adjoin ℚ S) FN)).scaleRoots (M : FN) with hq
  have hqmonic : q.Monic := (Polynomial.monic_scaleRoots_iff _).mpr (hmonic.map _)
  have hqroot : q.eval ((M : FN) * x) = 0 := by
    rw [hq, Polynomial.scaleRoots_eval_mul, Polynomial.eval_map, hroot, mul_zero]
  have hqcoeff : ∀ i, q.coeff i ∈ Algebra.adjoin ℤℓ S := by
    intro i
    rw [hq, Polynomial.coeff_scaleRoots, Polynomial.coeff_map, hmonic.natDegree_map]
    by_cases hi : i < p.natDegree
    · obtain ⟨k, hk⟩ := hdvd i hi.le
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt hi
      have hdeg : p.natDegree - i = d + 1 := by omega
      rw [hdeg, pow_succ, hk, Subalgebra.algebraMap_def, Algebra.algebraMap_self_apply,
        show (p.coeff i : FN) * ((((n i * k : ℕ) : FN)) ^ d * ((n i * k : ℕ) : FN))
          = (((n i * k : ℕ) : FN) ^ d * (k : FN)) * ((n i : FN) * (p.coeff i : FN)) by
            push_cast; ring]
      exact mul_mem (mul_mem (pow_mem (Subalgebra.natCast_mem _ _) d)
        (Subalgebra.natCast_mem _ _)) (hn i)
    · rcases (not_lt.mp hi).lt_or_eq with hlt | heq
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt, map_zero, zero_mul]
        exact zero_mem _
      · rw [← heq, hmonic.coeff_natDegree, map_one, one_mul, Nat.sub_self, pow_zero]
        exact one_mem _
  have hlifts : q ∈ Polynomial.lifts (algebraMap (Algebra.adjoin ℤℓ S) FN) :=
    (Polynomial.lifts_iff_coeff_lifts q).mpr fun i => ⟨⟨q.coeff i, hqcoeff i⟩, rfl⟩
  obtain ⟨q', hq'q, -, hq'monic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts hqmonic
  refine ⟨M, hM0, (mem_chartAlg_iff N ℓ).mpr ⟨q', hq'monic, ?_⟩⟩
  rw [Polynomial.eval₂_eq_eval_map, hq'q, hqroot]

theorem exists_eq_inv_nat_tmul (S : Set FN) (z : ℚ ⊗[ℤℓ] ↥(chartAlg N ℓ S)) :
    ∃ n : ℕ, n ≠ 0 ∧ ∃ a : chartAlg N ℓ S, z = ((n : ℚ)⁻¹) ⊗ₜ a := by
  have key : ∀ (m k : ℕ), k ≠ 0 → ∀ a : chartAlg N ℓ S,
      ((m : ℚ)⁻¹) ⊗ₜ[ℤℓ] a = (((m * k : ℕ) : ℚ)⁻¹) ⊗ₜ[ℤℓ] ((k : ℤℓ) • a) := by
    intro m k hk a
    rw [← TensorProduct.smul_tmul]
    congr 1
    rw [Algebra.smul_def]
    have : (algebraMap ℤℓ ℚ) (k : ℤℓ) = (k : ℚ) := map_natCast _ k
    rw [this]
    have hk' : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hk
    push_cast
    field_simp
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨1, one_ne_zero, 0, by simp⟩
  | tmul q a =>
    refine ⟨q.den, q.den_nz, (q.num : ℤℓ) • a, ?_⟩
    rw [← TensorProduct.smul_tmul]
    congr 1
    rw [Algebra.smul_def]
    have : (algebraMap ℤℓ ℚ) (q.num : ℤℓ) = (q.num : ℚ) := map_intCast _ q.num
    rw [this, ← div_eq_mul_inv, Rat.num_div_den]
  | add y z hy hz =>
    obtain ⟨m, hm0, a, rfl⟩ := hy
    obtain ⟨n, hn0, b, rfl⟩ := hz
    refine ⟨m * n, mul_ne_zero hm0 hn0, (n : ℤℓ) • a + (m : ℤℓ) • b, ?_⟩
    rw [TensorProduct.tmul_add, ← key m n hn0 a, mul_comm m n, ← key n m hm0 b]

def ratTensorToField (S : Set FN) : ℚ ⊗[ℤℓ] ↥(chartAlg N ℓ S) →ₐ[ℚ] FN :=
  Algebra.TensorProduct.lift (Algebra.ofId ℚ FN) ((chartAlg N ℓ S).val) (fun _ _ => Commute.all _ _)

theorem ratTensorToField_tmul (S : Set FN) (q : ℚ) (a : chartAlg N ℓ S) :
    ratTensorToField N ℓ S (q ⊗ₜ a) = q • (a : FN) := by
  simp [ratTensorToField, Algebra.smul_def]

theorem ratTensorToField_injective (S : Set FN) :
    Function.Injective (ratTensorToField N ℓ S) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨n, hn0, a, rfl⟩ := exists_eq_inv_nat_tmul N ℓ S z
  rw [ratTensorToField_tmul, smul_eq_zero] at hz
  rcases hz with h | h
  · exact absurd h (inv_ne_zero (Nat.cast_ne_zero.mpr hn0))
  · rw [show a = 0 from Subtype.ext h, TensorProduct.tmul_zero]

theorem range_ratTensorToField (S : Set FN) :
    (ratTensorToField N ℓ S).range = AlgebraicCurve.CurveModel.chartRing ℚ S := by
  apply le_antisymm
  · rintro x ⟨z, rfl⟩
    obtain ⟨n, hn0, a, rfl⟩ := exists_eq_inv_nat_tmul N ℓ S z
    change ratTensorToField N ℓ S _ ∈ _
    rw [ratTensorToField_tmul]
    exact Subalgebra.smul_mem _ (chartAlg_le_chartRing N ℓ S a.2) _
  · intro x hx
    obtain ⟨n, hn0, hnx⟩ := exists_nat_mul_mem_chartAlg N ℓ S hx
    refine ⟨((n : ℚ)⁻¹) ⊗ₜ ⟨(n : FN) * x, hnx⟩, ?_⟩
    change ratTensorToField N ℓ S _ = x
    rw [ratTensorToField_tmul]
    change ((n : ℚ)⁻¹) • ((n : FN) * x) = x
    rw [Algebra.smul_def, map_inv₀, map_natCast, ← mul_assoc,
      inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hn0), one_mul]

theorem exists_algEquiv_rat_tensor_chartAlg_chartRing (S : Set FN) :
    ∃ e : ℚ ⊗[ℤℓ] ↥(chartAlg N ℓ S) ≃ₐ[ℚ] ↥(AlgebraicCurve.CurveModel.chartRing ℚ S),
      ∀ (q : ℚ) (b : ↥(chartAlg N ℓ S)),
        ((e (q ⊗ₜ b) : ↥(AlgebraicCurve.CurveModel.chartRing ℚ S)) : FN) = q • (b : FN) := by
  refine ⟨(AlgEquiv.ofInjective _ (ratTensorToField_injective N ℓ S)).trans
    (Subalgebra.equivOfEq _ _ (range_ratTensorToField N ℓ S)), fun q b => ?_⟩
  exact ratTensorToField_tmul N ℓ S q b

end IgusaScheme
end ModularCurve

open scoped TensorProduct in
open _root_.ModularCurve _root_.P2MW.S_ModularCurve_IgusaScheme_exists_algEquiv_rat_tensor_chartAlg_chartRing.ModularCurve _root_.ModularCurve.IgusaScheme _root_.P2MW.S_ModularCurve_IgusaScheme_exists_algEquiv_rat_tensor_chartAlg_chartRing.ModularCurve.IgusaScheme in
theorem solution
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] (S : Set ↥(modularFunctionFieldFull N)) :
    ∃ e : ℚ ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlg N ℓ S) ≃ₐ[ℚ]
        ↥(AlgebraicCurve.CurveModel.chartRing ℚ S),
      ∀ (q : ℚ) (b : ↥(chartAlg N ℓ S)),
        ((e (q ⊗ₜ b) : ↥(AlgebraicCurve.CurveModel.chartRing ℚ S)) : ↥(modularFunctionFieldFull N))
          = q • (b : ↥(modularFunctionFieldFull N)) :=
  ModularCurve.IgusaScheme.exists_algEquiv_rat_tensor_chartAlg_chartRing N ℓ S
end

end S_ModularCurve_IgusaScheme_exists_algEquiv_rat_tensor_chartAlg_chartRing
end P2MW
export P2MW.S_ModularCurve_IgusaScheme_exists_algEquiv_rat_tensor_chartAlg_chartRing (solution)
