-- Prove2me | solution 1 for GroundTheory.PAdicHodge.exists_pow_approx_cycl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:45:13.505236+00:00
-- url     : https://prove2.me/submissions/040cfee2-de3a-47ac-8bc8-4b101d58a778

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower
import Definitions.Def_GroundTheory_PAdicHodge_TiltValuation
import Definitions.Def_GroundTheory_PAdicHodge_FWCyclotomicNorm
import Theorems.Thm_GroundTheory_PAdicHodge_exists_eq_sum_sub_one_pow
import Theorems.Thm_GroundTheory_PAdicHodge_norm_coeff_mul_le_norm_sum
import Theorems.Thm_GroundTheory_PAdicHodge_norm_coeff_le_one
import Theorems.Thm_GroundTheory_PAdicHodge_norm_pow_sub_self_le
import Theorems.Thm_GroundTheory_PAdicHodge_not_isUnit_natCast_normInteger
import Theorems.Thm_GroundTheory_PAdicHodge_cycl_mono
import Theorems.Thm_GroundTheory_PAdicHodge_exists_isPrimitiveRoot
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_zero
import Theorems.Thm_GroundTheory_PAdicHodge_norm_eq_one_of_pow_eq_one
import Theorems.Thm_GroundTheory_PAdicHodge_norm_natCast_prime
import Theorems.Thm_GroundTheory_PAdicHodge_norm_sub_one_le_one
import Theorems.Thm_GroundTheory_PAdicHodge_pow_eq_one_mem_cycl
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_normTraceF__apply_b99e2e848285
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_normTrace__apply_81a03c79b867
import Theorems.Thm_UpperTheory_Reformulated_B_CapelliMiscellany_norm_natCast_prime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.normTrace_zero
attribute [local simp] P2M_GroundTheory_PAdicHodge_normTraceF__apply_b99e2e848285
attribute [local simp] P2M_GroundTheory_PAdicHodge_normTrace__apply_81a03c79b867



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open IntermediateField Polynomial
variable {p : ℕ} [Fact p.Prime]
namespace GroundTheory.PAdicHodge
theorem _root_.solution {n : ℕ} {x : PadicAlgCl p} (hx : x ∈ cycl p n) (hx1 : ‖x‖ ≤ 1) :
    ∃ y ∈ cycl p (n + 2), ‖y‖ ≤ 1 ∧ ‖x - y ^ p‖ ≤ ‖(p : PadicAlgCl p)‖ := by
  classical
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hx' : x ∈ cycl p (n + 1) := cycl_mono (Nat.le_succ n) hx
  obtain ⟨η, hη⟩ := exists_isPrimitiveRoot (p := p) (n + 2)
  have hζ : IsPrimitiveRoot (η ^ p) (p ^ (n + 1)) :=
    hη.pow (pow_pos hp0 _) (by ring)
  set ζ := η ^ p
  set d := Nat.totient (p ^ (n + 1))
  obtain ⟨a, ha⟩ := exists_eq_sum_sub_one_pow hζ hx'
  set b : ℕ → ℚ_[p] := fun i => if i < d then a i else 0
  have hsum : ∀ u : PadicAlgCl p, ∑ i ∈ Finset.range d, algebraMap ℚ_[p] (PadicAlgCl p) (a i) * u ^ i =
      ∑ i ∈ Finset.range d, algebraMap ℚ_[p] (PadicAlgCl p) (b i) * u ^ i := fun u =>
    Finset.sum_congr rfl fun i hi => by simp only [b, if_pos (Finset.mem_range.1 hi)]
  have hb1 : ∀ i, ‖b i‖ ≤ 1 := by
    intro i
    by_cases hi : i < d
    · simp only [b, if_pos hi]
      refine norm_coeff_le_one hζ hi ?_
      exact (norm_coeff_mul_le_norm_sum hζ a i (Finset.mem_range.2 hi)).trans (ha ▸ hx1)
    · simp [b, if_neg hi]
  rw [hsum] at ha
  have hηn : ‖η‖ = 1 := norm_eq_one_of_pow_eq_one (pow_ne_zero _ hp0.ne') hη.pow_eq_one
  have hη1 : ‖η - 1‖ ≤ 1 := norm_sub_one_le_one (pow_ne_zero _ hp0.ne') hη.pow_eq_one
  have hζn : ‖ζ‖ ≤ 1 := by rw [norm_pow, hηn, one_pow]
  set y := ∑ i ∈ Finset.range d, algebraMap ℚ_[p] (PadicAlgCl p) (b i) * (η - 1) ^ i
  have hy1 : ‖y‖ ≤ 1 := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
    rw [norm_mul, norm_pow, norm_algebraMap']
    exact mul_le_one₀ (hb1 i) (pow_nonneg (norm_nonneg _) _) (pow_le_one₀ (norm_nonneg _) hη1)
  have hymem : y ∈ cycl p (n + 2) := by
    refine sum_mem fun i _ => mul_mem (IntermediateField.algebraMap_mem _ _) (pow_mem (sub_mem ?_ (one_mem _)) _)
    exact pow_eq_one_mem_cycl hη.pow_eq_one
  refine ⟨y, hymem, hy1, ?_⟩

  set O := normInteger (PadicAlgCl p)
  have : Fact (¬IsUnit (p : O)) := ⟨not_isUnit_natCast_normInteger⟩
  set A : ℕ → O := fun i => ⟨algebraMap ℚ_[p] (PadicAlgCl p) (b i),
    mem_normInteger.2 (by rw [norm_algebraMap']; exact hb1 i)⟩
  set H : O := ⟨η, mem_normInteger.2 hηn.le⟩
  set Z : O := ⟨ζ, mem_normInteger.2 hζn⟩
  set X : O := ∑ i ∈ Finset.range d, A i * (Z - 1) ^ i
  set Y : O := ∑ i ∈ Finset.range d, A i * (H - 1) ^ i
  have hX : (X : PadicAlgCl p) = x := by
    rw [ha]; simp [X, A, Z, ζ]
  have hY : (Y : PadicAlgCl p) = y := by simp [Y, y, A, H]
  set mk := Ideal.Quotient.mk (Ideal.span {(p : O)})
  have hA : ∀ i, mk (A i) ^ p = mk (A i) := by
    intro i
    rw [← map_pow]
    refine (mk_eq_mk_iff_norm_sub_le (K := PadicAlgCl p)).2 ?_
    have : ((A i ^ p : O) : PadicAlgCl p) - (A i : PadicAlgCl p) =
        algebraMap ℚ_[p] (PadicAlgCl p) (b i ^ p - b i) := by simp [A]
    rw [this, norm_algebraMap', norm_natCast_prime]
    exact norm_pow_sub_self_le (hb1 i)
  have hH : (mk H - 1) ^ p = mk Z - 1 := by
    rw [sub_pow_char, one_pow, ← map_pow]
    congr 2
  have hmk : mk (Y ^ p) = mk X := by
    simp only [Y, X, map_pow, map_sum, map_mul, map_sub, map_one]
    rw [sum_pow_char]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_pow, hA, ← pow_mul, mul_comm i p, pow_mul, hH]
  have := (mk_eq_mk_iff_norm_sub_le (K := PadicAlgCl p)).1 hmk.symm
  rw [hX, Subring.coe_pow, hY] at this
  simpa using this
end GroundTheory.PAdicHodge
