-- Prove2me | solution 1 for Lean4LPD.PauliString.sum_norm_coeff_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:21:20.190336+00:00
-- url     : https://prove2.me/submissions/a76febad-eb9f-4713-a8c8-01e742248350

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Trace
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Coeff
public import Theorems.Thm_Lean4LPD_norm_iPow
public import Theorems.Thm_Lean4LPD_PauliString_herm_x
public import Theorems.Thm_Lean4LPD_PauliString_herm_z
public import Theorems.Thm_Lean4LPD_PauliString_trace_toMatrix_mul
public import Theorems.Thm_Lean4LPD_PauliString_mem_antiSites
public import Theorems.Thm_Lean4LPD_PauliString_mem_support
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_eq_phaseMul_iff
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_eq_self_iff
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_phase
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_x
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_z
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_zero
public import Theorems.Thm_Lean4LPD_PauliString_site_mul
public import Theorems.Thm_Lean4LPD_PauliString_site_one
public import Theorems.Thm_Lean4LPD_PauliString_site_phaseMul
public import Theorems.Thm_Lean4LPD_PauliString_sympForm_mul_self_right
public import Theorems.Thm_Lean4LPD_PauliString_sympForm_phaseMul_left
public import Theorems.Thm_Lean4LPD_PauliString_sympForm_phaseMul_right
public import Theorems.Thm_Lean4LPD_PauliString_sympForm_self
public import Theorems.Thm_Lean4LPD_PauliString_toMatrix_one
public import Theorems.Thm_Lean4LPD_PauliString_toMatrix_phaseMul
public import Theorems.Thm_Lean4LPD_PauliString_weight_one
public import Theorems.Thm_Lean4LPD_PauliString_weight_phaseMul
public import Theorems.Thm_Lean4LPD_bits_add_eq_zero_iff
public import Theorems.Thm_Lean4LPD_conj_negOnePow
public import Theorems.Thm_Lean4LPD_iPow_signPhase
public import Theorems.Thm_Lean4LPD_iPow_two
public import Theorems.Thm_Lean4LPD_negOnePow_add
public import Theorems.Thm_Lean4LPD_negOnePow_mul_self
public import Theorems.Thm_Lean4LPD_negOnePow_one
public import Theorems.Thm_Lean4LPD_negOnePow_zero
public import Theorems.Thm_Lean4LPD_star_negOnePow
attribute [local simp] Lean4LPD.PauliString.mem_antiSites
attribute [local simp] Lean4LPD.PauliString.mem_support
attribute [local simp] Lean4LPD.PauliString.phaseMul_eq_phaseMul_iff
attribute [local simp] Lean4LPD.PauliString.phaseMul_eq_self_iff
attribute [local simp] Lean4LPD.PauliString.phaseMul_phase
attribute [local simp] Lean4LPD.PauliString.phaseMul_x
attribute [local simp] Lean4LPD.PauliString.phaseMul_z
attribute [local simp] Lean4LPD.PauliString.phaseMul_zero
attribute [local simp] Lean4LPD.PauliString.site_mul
attribute [local simp] Lean4LPD.PauliString.site_one
attribute [local simp] Lean4LPD.PauliString.site_phaseMul
attribute [local simp] Lean4LPD.PauliString.sympForm_mul_self_right
attribute [local simp] Lean4LPD.PauliString.sympForm_phaseMul_left
attribute [local simp] Lean4LPD.PauliString.sympForm_phaseMul_right
attribute [local simp] Lean4LPD.PauliString.sympForm_self
attribute [local simp] Lean4LPD.PauliString.toMatrix_one
attribute [local simp] Lean4LPD.PauliString.toMatrix_phaseMul
attribute [local simp] Lean4LPD.PauliString.weight_one
attribute [local simp] Lean4LPD.PauliString.weight_phaseMul
attribute [local simp] Lean4LPD.conj_negOnePow
attribute [local simp] Lean4LPD.iPow_signPhase
attribute [local simp] Lean4LPD.iPow_two
attribute [local simp] Lean4LPD.negOnePow_mul_self
attribute [local simp] Lean4LPD.negOnePow_one
attribute [local simp] Lean4LPD.negOnePow_zero
attribute [local simp] Lean4LPD.star_negOnePow


attribute [local simp] Lean4LPD.norm_iPow
attribute [local simp] Lean4LPD.PauliString.herm_x
attribute [local simp] Lean4LPD.PauliString.herm_z
section
@[expose] public section
namespace Lean4LPD
open Finset
namespace PauliString
variable {n : ℕ}
private lemma sum_sq_char (x : Bits n) (O : Matrix (Bits n) (Bits n) ℂ) :
    ∑ z : Bits n, ‖∑ b : Bits n, negOnePow (z ⬝ᵥ b) * O b (b + x)‖ ^ 2
      = 2 ^ n * ∑ b : Bits n, ‖O b (b + x)‖ ^ 2 := by
  have key : ∀ z : Bits n, ((‖∑ b : Bits n, negOnePow (z ⬝ᵥ b) * O b (b + x)‖ : ℝ) : ℂ) ^ 2
      = ∑ b : Bits n, ∑ c : Bits n,
          negOnePow (z ⬝ᵥ (b + c)) * (O b (b + x) * (starRingEnd ℂ) (O c (c + x))) := by
    intro z
    rw [← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
    rw [map_mul, conj_negOnePow, dotProduct_add, negOnePow_add]
    ring
  have hchar : ∀ b c : Bits n, (∑ z : Bits n, negOnePow (z ⬝ᵥ (b + c)))
      = if b = c then (2 : ℂ) ^ n else 0 := by
    intro b c
    rw [Finset.sum_congr rfl fun z (_ : z ∈ univ) =>
        congrArg negOnePow (dotProduct_comm z (b + c)), char_sum]
    by_cases h : b = c
    · rw [if_pos (by rw [h]; exact bits_add_self c), if_pos h]
    · rw [if_neg fun hc => h (bits_add_eq_zero_iff.1 hc), if_neg h]
  have main : ((∑ z : Bits n, ‖∑ b : Bits n, negOnePow (z ⬝ᵥ b) * O b (b + x)‖ ^ 2 : ℝ) : ℂ)
      = ((2 ^ n * ∑ b : Bits n, ‖O b (b + x)‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    calc ∑ z : Bits n, ((‖∑ b : Bits n, negOnePow (z ⬝ᵥ b) * O b (b + x)‖ : ℝ) : ℂ) ^ 2
        = ∑ z : Bits n, ∑ b : Bits n, ∑ c : Bits n,
            negOnePow (z ⬝ᵥ (b + c)) * (O b (b + x) * (starRingEnd ℂ) (O c (c + x))) :=
          Finset.sum_congr rfl fun z _ => key z
      _ = ∑ b : Bits n, ∑ c : Bits n, ∑ z : Bits n,
            negOnePow (z ⬝ᵥ (b + c)) * (O b (b + x) * (starRingEnd ℂ) (O c (c + x))) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun b _ => Finset.sum_comm
      _ = ∑ b : Bits n, ∑ c : Bits n,
            (if b = c then (2 : ℂ) ^ n else 0)
              * (O b (b + x) * (starRingEnd ℂ) (O c (c + x))) :=
          Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by
            rw [← Finset.sum_mul, hchar b c]
      _ = 2 ^ n * ∑ b : Bits n, ((‖O b (b + x)‖ : ℝ) : ℂ) ^ 2 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.sum_eq_single b]
          · rw [if_pos rfl, ← Complex.mul_conj']
          · intro c _ hc
            rw [if_neg (Ne.symm hc), zero_mul]
          · intro h
            exact absurd (Finset.mem_univ _) h
  exact_mod_cast main
end PauliString
end Lean4LPD
end
end

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
open Lean4LPD.PauliString
variable {n : ℕ}
namespace Lean4LPD.PauliString
theorem _root_.solution (O : Matrix (Bits n) (Bits n) ℂ) :
    ∑ p : PauliIndex n, ‖coeff O p‖ ^ 2 = pauliNormSq O := by
  have hnorm : ∀ p : PauliIndex n,
      ‖coeff O p‖ ^ 2
        = (((2 : ℝ) ^ n)⁻¹) ^ 2 * ‖∑ b : Bits n, negOnePow (p.2 ⬝ᵥ b) * O b (b + p.1)‖ ^ 2 := by
    intro p
    rw [coeff, trace_toMatrix_mul, norm_mul, norm_mul, mul_pow, mul_pow, norm_iPow, one_pow,
      one_mul, herm_x, herm_z]
    congr 2
    rw [norm_inv, norm_pow, Complex.norm_ofNat]
  rw [Finset.sum_congr rfl fun p (_ : p ∈ univ) => hnorm p, ← Finset.mul_sum,
    Fintype.sum_prod_type]
  have hx : ∀ x : Bits n, (∑ z : Bits n, ‖∑ b : Bits n, negOnePow (z ⬝ᵥ b) * O b (b + x)‖ ^ 2)
      = 2 ^ n * ∑ b : Bits n, ‖O b (b + x)‖ ^ 2 := fun x => sum_sq_char x O
  rw [Finset.sum_congr rfl fun x (_ : x ∈ univ) => hx x, ← Finset.mul_sum, Finset.sum_comm]
  have hswap : ∀ b : Bits n, (∑ x : Bits n, ‖O b (b + x)‖ ^ 2) = ∑ a : Bits n, ‖O b a‖ ^ 2 :=
    fun b => Fintype.sum_equiv (Equiv.addLeft b) _ _ fun x => rfl
  rw [Finset.sum_congr rfl fun b (_ : b ∈ univ) => hswap b, pauliNormSq, ← mul_assoc,
    show (((2 : ℝ) ^ n)⁻¹) ^ 2 * 2 ^ n = ((2 : ℝ) ^ n)⁻¹ from by
      have h2 : ((2 : ℝ) ^ n) ≠ 0 := by positivity
      field_simp]
end Lean4LPD.PauliString
