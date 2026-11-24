-- Prove2me | solution 1 for GlobalTheory.SW.ip_self_nonneg_and_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:47:18.382787+00:00
-- url     : https://prove2.me/submissions/3c2b1fd6-6114-4105-a857-289d61f6d826

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FinsumQuotientOfLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInnerProductSelfNonnegBounds
import Theorems.Thm_GlobalTheory_SW_IpPos_apply_out_mk
import Theorems.Thm_GlobalTheory_SW_IpPos_hasLevel_mul
import Theorems.Thm_GlobalTheory_SW_IpPos_ip_eq_sum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
namespace GlobalTheory.SW.IpPos
open NumberField
variable {K κ ι : Type} [Field K] [NumberField K] [Fintype κ] [Fintype ι]
end GlobalTheory.SW.IpPos
open Matrix Complex in
open scoped ComplexConjugate Real in
open NumberField in
variable {K κ ι : Type} [Field K] [NumberField K] [Fintype κ] [Fintype ι] in
private lemma schwartzBruhatInnerProduct_self_eq_lemma {R : ℕ} (hR : 0 < R) {φ : Matrix κ ι K → ℂ}
    (hφ : _root_.GlobalTheory.SW.HasLevel R φ) :
    _root_.GlobalTheory.SW.ip φ φ =
      (((R : ℝ) ^ (Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι)))⁻¹ *
      ∑ q ∈ (_root_.GlobalTheory.SW.IpPos.classes_finite_card (K := K) (κ := κ) (ι := ι) hR).1.toFinset,
        ‖φ q.out‖ ^ 2 : ℝ) := by
  rw [_root_.GlobalTheory.SW.IpPos.ip_eq_sum hR hφ hφ]
  simp_rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl
end

set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open Matrix Complex
open scoped ComplexConjugate Real
namespace _root_.GlobalTheory.SW
theorem _root_.solution : ∀ (K κ ι : Type) [Field K] [NumberField K]
    [Fintype κ] [Fintype ι] (R : ℕ) (φ : Matrix κ ι K → ℂ), 0 < R → _root_.GlobalTheory.SW.HasLevel R φ →
    (_root_.GlobalTheory.SW.ip φ φ).im = 0 ∧ 0 ≤ (_root_.GlobalTheory.SW.ip φ φ).re ∧
    (∀ x, ‖φ x‖ ^ 2 ≤ (R : ℝ) ^ (Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι)) *
      (_root_.GlobalTheory.SW.ip φ φ).re) ∧
    (∀ B : ℝ, (∀ x, ‖φ x‖ ≤ B) → (_root_.GlobalTheory.SW.ip φ φ).re ≤
      (R : ℝ) ^ (Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι)) * B ^ 2) ∧
    (∃ B : ℝ, ∀ x, ‖φ x‖ ≤ B) ∧ ∀ ψ, _root_.GlobalTheory.SW.IsSB ψ →
      ‖_root_.GlobalTheory.SW.ip φ ψ‖ ^ 2 ≤
        (_root_.GlobalTheory.SW.ip φ φ).re * (_root_.GlobalTheory.SW.ip ψ ψ).re := by
  intro K κ ι _ _ _ _ R φ hR hφ
  set N := Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι)
  have hfc := _root_.GlobalTheory.SW.IpPos.classes_finite_card (K := K) (κ := κ) (ι := ι) hR
  set s := hfc.1.toFinset with hs
  set Sφ := ∑ q ∈ s, ‖φ q.out‖ ^ 2 with hSφ
  have hc : (0 : ℝ) < (R : ℝ) ^ N := by positivity
  have hip : _root_.GlobalTheory.SW.ip φ φ = (((R : ℝ) ^ N)⁻¹ * Sφ : ℝ) :=
    schwartzBruhatInnerProduct_self_eq_lemma hR hφ
  have hre : (_root_.GlobalTheory.SW.ip φ φ).re = ((R : ℝ) ^ N)⁻¹ * Sφ := by
    rw [hip, Complex.ofReal_re]
  have hS0 : 0 ≤ Sφ := Finset.sum_nonneg fun _ _ => by positivity
  have hpt : ∀ x, ‖φ x‖ ^ 2 ≤ (R : ℝ) ^ N * (_root_.GlobalTheory.SW.ip φ φ).re := by
    intro x
    rw [hre, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
    by_cases hx : φ x = 0
    · simpa [hx] using hS0
    · have hq : (QuotientAddGroup.mk x : Matrix κ ι K ⧸ _root_.GlobalTheory.SW.perSub K κ ι R) ∈ s := by
        rw [hs, Set.Finite.mem_toFinset]
        show _root_.GlobalTheory.SW.IntM _
        exact hφ.1 _ (by rwa [_root_.GlobalTheory.SW.IpPos.apply_out_mk hφ])
      have h := Finset.single_le_sum (f := fun q => ‖φ q.out‖ ^ 2) (fun _ _ => by positivity) hq
      simpa only [_root_.GlobalTheory.SW.IpPos.apply_out_mk hφ] using h
  refine ⟨by rw [hip, Complex.ofReal_im], by rw [hre]; positivity, hpt, fun B hB => ?_,
    ⟨√((R : ℝ) ^ N * (_root_.GlobalTheory.SW.ip φ φ).re), fun x => by
      simpa using Real.abs_le_sqrt (hpt x)⟩, fun ψ hψ => ?_⟩
  · have h1 : Sφ ≤ s.card • B ^ 2 :=
      Finset.sum_le_card_nsmul _ _ _ (fun q _ => pow_le_pow_left₀ (norm_nonneg _) (hB _) 2)
    have hcard : (s.card : ℝ) ≤ ((R : ℝ) ^ N) ^ 2 := by
      rw [hs, ← Set.ncard_eq_toFinset_card _ hfc.1]
      exact_mod_cast hfc.2
    rw [nsmul_eq_mul] at h1
    rw [hre]
    calc ((R : ℝ) ^ N)⁻¹ * Sφ ≤ ((R : ℝ) ^ N)⁻¹ * (((R : ℝ) ^ N) ^ 2 * B ^ 2) := by
          gcongr
          exact h1.trans (mul_le_mul_of_nonneg_right hcard (sq_nonneg B))
      _ = (R : ℝ) ^ N * B ^ 2 := by field_simp
  · obtain ⟨S, hS, hψS⟩ := hψ
    have hRS : 0 < R * S := Nat.mul_pos hR hS
    have hφ' := _root_.GlobalTheory.SW.IpPos.hasLevel_mul hφ S
    have hψ' : _root_.GlobalTheory.SW.HasLevel (R * S) ψ := by
      rw [mul_comm]; exact _root_.GlobalTheory.SW.IpPos.hasLevel_mul hψS R
    rw [_root_.GlobalTheory.SW.IpPos.ip_eq_sum hRS hφ' hψ',
      schwartzBruhatInnerProduct_self_eq_lemma hRS hφ', schwartzBruhatInnerProduct_self_eq_lemma hRS hψ',
      Complex.ofReal_re, Complex.ofReal_re, norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
    set t := (_root_.GlobalTheory.SW.IpPos.classes_finite_card (K := K) (κ := κ) (ι := ι) hRS).1.toFinset
    set d : ℝ := ((R * S : ℕ) : ℝ) ^ N
    have hcs : ‖∑ q ∈ t, φ q.out * conj (ψ q.out)‖ ^ 2 ≤
        (∑ q ∈ t, ‖φ q.out‖ ^ 2) * ∑ q ∈ t, ‖ψ q.out‖ ^ 2 := by
      calc _ ≤ (∑ q ∈ t, ‖φ q.out‖ * ‖ψ q.out‖) ^ 2 := by
            gcongr
            refine (norm_sum_le _ _).trans (le_of_eq ?_)
            simp [Complex.norm_conj]
        _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    calc (d⁻¹ * ‖∑ q ∈ t, φ q.out * conj (ψ q.out)‖) ^ 2
        = d⁻¹ * d⁻¹ * ‖∑ q ∈ t, φ q.out * conj (ψ q.out)‖ ^ 2 := by ring
      _ ≤ d⁻¹ * d⁻¹ * ((∑ q ∈ t, ‖φ q.out‖ ^ 2) * ∑ q ∈ t, ‖ψ q.out‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hcs (by positivity)
      _ = _ := by ring
end _root_.GlobalTheory.SW
