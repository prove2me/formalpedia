-- Prove2me | solution 1 for ModularCurve.SiegelUnit.exists_gamma1_peaked_auxiliary_form_twelve_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/2be0411c-3adb-52cb-82e4-c1b9116c68b4

import Mathlib
import Definitions.Def_ModularCurve_SiegelFunction
import Theorems.Thm_ModularCurve_SiegelUnit_exists_peaked_exponent
import Theorems.Thm_CongruenceSubgroup_mem_or_neg_mem_Gamma1_iff_and_exists_T_zpow_S_inv_iff
import Theorems.Thm_ModularCurve_SiegelUnit_exists_modularForm_gamma1_coe_eq_prod_siegelFun_pow_mul_discriminant_pow
import Theorems.Thm_ModularCurve_SiegelUnit_qExpansion_one_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow
import Theorems.Thm_ModularCurve_SiegelUnit_isIntegral_qExpansion_slash_S_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_SiegelUnit_exists_gamma1_peaked_auxiliary_form_twelve_dvd
p2m_attr_erase "simp" "ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ"

set_option autoImplicit false

open scoped MatrixGroups ModularForm

namespace UEven

theorem addOrderOf_dvd_sum_of_invariant {N : ℕ} [NeZero N] (r : ZMod N) (f : ZMod N → ℕ)
    (hf : ∀ s, f (s + r) = f s) : addOrderOf r ∣ ∑ s : ZMod N, f s := by
  classical

  set H : AddSubgroup (ZMod N) := AddSubgroup.zmultiples r with hH
  have hinvn : ∀ (k : ℕ) (s : ZMod N), f (s + k • r) = f s := by
    intro k
    induction k with
    | zero => intro s; rw [zero_smul, add_zero]
    | succ k ih => intro s; rw [succ_nsmul, ← add_assoc, hf, ih]
  have hinv : ∀ h ∈ H, ∀ s, f (s + h) = f s := by
    intro h hh s
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hh

    have hn : 0 < addOrderOf r := addOrderOf_pos r
    obtain ⟨k', hk'⟩ : ∃ k' : ℕ, (k' : ℤ) • r = k • r := by
      refine ⟨(k % (addOrderOf r : ℤ)).toNat, ?_⟩
      have h0 : 0 ≤ k % (addOrderOf r : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hn.ne')
      rw [Int.toNat_of_nonneg h0]
      have : k % (addOrderOf r : ℤ) = k - (k / (addOrderOf r : ℤ)) * (addOrderOf r : ℤ) := by
        have := Int.emod_add_mul_ediv k (addOrderOf r : ℤ)
        have := mul_comm (addOrderOf r : ℤ) (k / (addOrderOf r : ℤ))
        omega
      rw [this, sub_zsmul, mul_zsmul, natCast_zsmul, addOrderOf_nsmul_eq_zero, zsmul_zero, neg_zero, add_zero]
    rw [← hk', natCast_zsmul]
    exact hinvn k' s

  let π : ZMod N → ZMod N ⧸ H := QuotientAddGroup.mk
  have hfib : ∀ c : ZMod N ⧸ H, ∑ s ∈ Finset.univ.filter (fun s => π s = c), f s = Nat.card H * f (Quotient.out c) := by
    intro c
    have hconst : ∀ s ∈ Finset.univ.filter (fun s => π s = c), f s = f (Quotient.out c) := by
      intro s hs
      rw [Finset.mem_filter] at hs
      have hπ : π (Quotient.out c) = c := Quotient.out_eq c
      have : π s = π (Quotient.out c) := hs.2.trans hπ.symm
      have hmem : -Quotient.out c + s ∈ H := QuotientAddGroup.eq.mp this.symm
      have := hinv _ hmem (Quotient.out c)
      rwa [add_neg_cancel_left] at this
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul]
    congr 1

    rw [← Nat.card_eq_finsetCard]
    have e : ↥H ≃ {s : ZMod N // s ∈ Finset.univ.filter (fun s => π s = c)} :=
      { toFun := fun h => ⟨Quotient.out c + h, by
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          have e1 : π (Quotient.out c) = c := Quotient.out_eq c
          have e2 : π (Quotient.out c + h) = π (Quotient.out c) := by
            apply Eq.symm
            apply QuotientAddGroup.eq.mpr
            rw [neg_add_cancel_left]; exact h.2
          exact e2.trans e1⟩
        invFun := fun s => ⟨-Quotient.out c + s.1, by
          have hs := s.2
          rw [Finset.mem_filter] at hs
          have : π s.1 = π (Quotient.out c) := hs.2.trans (Quotient.out_eq c).symm
          exact QuotientAddGroup.eq.mp this.symm⟩
        left_inv := fun h => by ext; simp
        right_inv := fun s => by ext; simp }
    exact (Nat.card_congr e).symm
  rw [← Finset.sum_fiberwise Finset.univ π f]
  have hcard : Nat.card H = addOrderOf r := Nat.card_zmultiples r
  rw [← hcard]
  apply Finset.dvd_sum
  intro c _
  rw [hfib c]
  exact dvd_mul_right _ _

theorem gcd_dvd_weight (N v : ℕ) : ((Nat.gcd N v : ℕ) : ℤ) ∣ 6 * (v : ℤ) ^ 2 - 6 * (N : ℤ) * (v : ℤ) + (N : ℤ) ^ 2 := by
  have h1 : ((Nat.gcd N v : ℕ) : ℤ) ∣ (v : ℤ) := Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right N v)
  have h2 : ((Nat.gcd N v : ℕ) : ℤ) ∣ (N : ℤ) := Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left N v)
  refine dvd_add (dvd_sub ?_ ?_) ?_
  · exact dvd_mul_of_dvd_right (dvd_pow h1 two_ne_zero) _
  · exact dvd_mul_of_dvd_right h1 _
  · exact dvd_pow h2 two_ne_zero

theorem natCast_dvd_sum_weight {N : ℕ} [NeZero N] (m : ZMod N → ZMod N → ℕ)
    (hm : ∀ r s : ZMod N, m r (s + r) = m r s) :
    (N : ℤ) ∣ ∑ r : ZMod N, ∑ s : ZMod N,
      (m r s : ℤ) * (6 * (r.val : ℤ) ^ 2 - 6 * (N : ℤ) * (r.val : ℤ) + (N : ℤ) ^ 2) := by
  apply Finset.dvd_sum
  intro r _
  rw [← Finset.sum_mul]

  have h1 : ((addOrderOf r : ℕ) : ℤ) ∣ ∑ s : ZMod N, (m r s : ℤ) := by
    have := addOrderOf_dvd_sum_of_invariant r (m r) (fun s => hm r s)
    have h := Int.natCast_dvd_natCast.mpr this
    push_cast at h
    exact h
  have h2 := gcd_dvd_weight N r.val
  have hN : (N : ℤ) = ((addOrderOf r : ℕ) : ℤ) * ((Nat.gcd N r.val : ℕ) : ℤ) := by
    have hr : (r : ZMod N) = ((r.val : ℕ) : ZMod N) := (ZMod.natCast_zmod_val r).symm
    have ho : addOrderOf r = N / Nat.gcd N r.val := by
      conv_lhs => rw [hr]
      exact ZMod.addOrderOf_coe r.val (NeZero.ne N)
    rw [ho]
    exact_mod_cast (Nat.div_mul_cancel (Nat.gcd_dvd_left N r.val)).symm
  have := mul_dvd_mul h1 h2
  rwa [← hN] at this

theorem isIntegral_pow_mul_of_le {N : ℕ} {a b : ℕ} (hab : a ≤ b) {z : ℂ}
    (h : IsIntegral ℤ ((N : ℂ) ^ a * z)) : IsIntegral ℤ ((N : ℂ) ^ b * z) := by
  have hN : IsIntegral ℤ ((N : ℂ) ^ (b - a)) := by
    have : IsIntegral ℤ (N : ℂ) := by
      have := isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (N : ℤ))
      simpa using this
    exact this.pow _
  have : (N : ℂ) ^ b * z = (N : ℂ) ^ (b - a) * ((N : ℂ) ^ a * z) := by
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hab]
  rw [this]
  exact hN.mul h

end UEven

open scoped MatrixGroups ModularForm in
theorem solution (N : ℕ) (hN : 2 ≤ N) :
    ∃ (w : ℤ) (m₀ a : ℕ) (δ : ℝ)
      (ϑ : ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) w),
      12 ∣ w ∧ w < 12 * (m₀ : ℤ) ∧ 0 < δ ∧
      (∀ n : ℕ, IsIntegral ℤ ((N : ℂ) ^ a * (UpperHalfPlane.qExpansion (N : ℝ)
        ((⇑ϑ : UpperHalfPlane → ℂ) ∣[w] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ))).coeff n)) ∧
      (∀ n : ℕ, n < m₀ → (UpperHalfPlane.qExpansion 1 (⇑ϑ : UpperHalfPlane → ℂ)).coeff n = 0) ∧
      (UpperHalfPlane.qExpansion 1 (⇑ϑ : UpperHalfPlane → ℂ)).coeff m₀ ≠ 0 ∧
      IsIntegral ℤ ((N : ℂ) ^ a *
        ((UpperHalfPlane.qExpansion 1 (⇑ϑ : UpperHalfPlane → ℂ)).coeff m₀)⁻¹) ∧
      (∀ n : ℕ, IsIntegral ℤ ((N : ℂ) ^ a *
        (UpperHalfPlane.qExpansion 1 (⇑ϑ : UpperHalfPlane → ℂ)).coeff n)) ∧
      ∀ β : SL(2, ℤ),
        (β ∉ CongruenceSubgroup.Gamma1 N ∧ -β ∉ CongruenceSubgroup.Gamma1 N) →
        (∀ j : ℤ, β * ModularGroup.T ^ j * ModularGroup.S⁻¹ ∉ CongruenceSubgroup.Gamma1 N ∧
          -(β * ModularGroup.T ^ j * ModularGroup.S⁻¹) ∉ CongruenceSubgroup.Gamma1 N) →
        ((⇑ϑ : UpperHalfPlane → ℂ) ∣[w] (β : GL (Fin 2) ℝ)) =O[UpperHalfPlane.atImInfty]
          fun τ : UpperHalfPlane => Real.exp (-(2 * Real.pi * ((m₀ : ℝ) + δ)) * τ.im) := by
  classical
  haveI : NeZero N := ⟨by omega⟩

  obtain ⟨m, Ord, hOrd, hm00, hminv, hpos, hpeak⟩ := ModularCurve.SiegelUnit.exists_peaked_exponent N hN
  set t : ℕ := ∑ x : ZMod N, ∑ y : ZMod N, (Ord x y).natAbs with ht_def
  have hOrd_ge : ∀ x y : ZMod N, -(t : ℤ) ≤ Ord x y := by
    intro x y
    have h1 : (Ord x y).natAbs ≤ t := by
      rw [ht_def]
      exact (Finset.single_le_sum (f := fun y => (Ord x y).natAbs) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ y)).trans
        (Finset.single_le_sum (f := fun x => ∑ y, (Ord x y).natAbs) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ x))
    have h2 : -((Ord x y).natAbs : ℤ) ≤ Ord x y := by
      rw [Int.natCast_natAbs]; exact neg_abs_le _
    omega
  have hNpos : (0 : ℤ) < N := by exact_mod_cast (show 0 < N by omega)
  have htN : ∀ x y : ZMod N, 0 ≤ Ord x y + (N : ℤ) * t := by
    intro x y
    have := hOrd_ge x y
    have ht0 : (0 : ℤ) ≤ t := by exact_mod_cast Nat.zero_le t
    nlinarith

  have htF : ∀ β : SL(2, ℤ), 0 ≤ (∑ r : ZMod N, ∑ s : ZMod N, (m r s : ℤ) *
        (6 * ((r * ((β 0 0 : ℤ) : ZMod N) + s * ((β 1 0 : ℤ) : ZMod N)).val : ℤ) ^ 2
          - 6 * (N : ℤ) * ((r * ((β 0 0 : ℤ) : ZMod N) + s * ((β 1 0 : ℤ) : ZMod N)).val : ℤ) +
            (N : ℤ) ^ 2)) + (N : ℤ) * t := by
    intro β
    have := htN (((β 0 0 : ℤ) : ZMod N)) (((β 1 0 : ℤ) : ZMod N))
    rw [hOrd] at this
    exact this
  obtain ⟨ϑ, hϑ, hdecF⟩ :=
    ModularCurve.SiegelUnit.exists_modularForm_gamma1_coe_eq_prod_siegelFun_pow_mul_discriminant_pow
      N m hm00 hminv t htF

  have hS1 : Ord 1 0 = ∑ r : ZMod N, ∑ s : ZMod N,
      (m r s : ℤ) * (6 * (r.val : ℤ) ^ 2 - 6 * (N : ℤ) * (r.val : ℤ) + (N : ℤ) ^ 2) := by
    rw [hOrd]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
    rw [mul_one, mul_zero, add_zero]
  have hdvd : (N : ℤ) ∣ Ord 1 0 + (N : ℤ) * t := by
    rw [hS1]; exact dvd_add (UEven.natCast_dvd_sum_weight m hminv) (dvd_mul_right _ _)
  obtain ⟨M, hM⟩ := hdvd
  have hMpos : (t : ℤ) < M := by
    have : (N : ℤ) * t < (N : ℤ) * M := by rw [← hM]; linarith
    exact lt_of_mul_lt_mul_left this hNpos.le
  have hM0 : 0 ≤ M := by
    have : (0 : ℤ) ≤ t := by exact_mod_cast Nat.zero_le t
    omega
  obtain ⟨m₀, hm₀M⟩ : ∃ m₀ : ℕ, (m₀ : ℤ) = M := ⟨M.toNat, Int.toNat_of_nonneg hM0⟩
  have hm₀eq : (N : ℤ) * m₀ = (∑ r : ZMod N, ∑ s : ZMod N,
      (m r s : ℤ) * (6 * (r.val : ℤ) ^ 2 - 6 * (N : ℤ) * (r.val : ℤ) + (N : ℤ) ^ 2)) + (N : ℤ) * t := by
    rw [hm₀M, ← hM, hS1]

  obtain ⟨a₁, hz, hne, hinv₁, hint₁⟩ :=
    ModularCurve.SiegelUnit.qExpansion_one_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow
      N m hm00 t ϑ hϑ m₀ hm₀eq
  obtain ⟨a₂, hint₂⟩ :=
    ModularCurve.SiegelUnit.isIntegral_qExpansion_slash_S_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow
      N m t ϑ hϑ

  refine ⟨12 * (t : ℤ), m₀, max a₁ a₂, 1 / (N : ℝ), ϑ, dvd_mul_right _ _, ?_, ?_, ?_, hz, hne, ?_, ?_, ?_⟩
  · have : (t : ℤ) < m₀ := by rw [hm₀M]; exact hMpos
    linarith
  · have : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    positivity
  · intro n; exact UEven.isIntegral_pow_mul_of_le (le_max_right _ _) (hint₂ n)
  · exact UEven.isIntegral_pow_mul_of_le (le_max_left _ _) hinv₁
  · intro n; exact UEven.isIntegral_pow_mul_of_le (le_max_left _ _) (hint₁ n)
  · intro β hβ1 hβ2
    obtain ⟨hc1, hc2, hprim⟩ :=
      CongruenceSubgroup.mem_or_neg_mem_Gamma1_iff_and_exists_T_zpow_S_inv_iff N β
    set x : ZMod N := ((β 0 0 : ℤ) : ZMod N) with hx
    set y : ZMod N := ((β 1 0 : ℤ) : ZMod N) with hy
    have hnot1 : ¬ (y = 0 ∧ (x = 1 ∨ x = -1)) := fun h => (not_or.mpr hβ1) (hc1.mpr h)
    have hnot2 : ¬ (y = 1 ∨ y = -1) := fun h => by
      obtain ⟨j, hj⟩ := hc2.mpr h
      exact (not_or.mpr (hβ2 j)) hj
    have hlt : Ord 1 0 < Ord x y := hpeak x y hprim hnot1 hnot2
    refine (hdecF β).trans ?_
    refine Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall fun τ => ?_)
    rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.abs_exp, Real.abs_exp, Real.exp_le_exp]
    have hsum : (∑ r : ZMod N, ∑ s : ZMod N, (m r s : ℤ) *
        (6 * ((r * x + s * y).val : ℤ) ^ 2 - 6 * (N : ℤ) * ((r * x + s * y).val : ℤ) + (N : ℤ) ^ 2)) =
          Ord x y := (hOrd x y).symm
    rw [hsum]
    have hτ : 0 ≤ τ.im := τ.im_pos.le
    have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hkey : (m₀ : ℝ) + 1 / (N : ℝ) ≤ ((Ord x y : ℤ) : ℝ) / (N : ℝ) + (t : ℝ) := by
      have hZ : (N : ℤ) * m₀ + 1 ≤ Ord x y + (N : ℤ) * t := by
        rw [hm₀M, ← hM]; omega
      have hR : (N : ℝ) * m₀ + 1 ≤ ((Ord x y : ℤ) : ℝ) + (N : ℝ) * t := by exact_mod_cast hZ
      rw [← sub_nonneg]
      have : ((Ord x y : ℤ) : ℝ) / N + t - ((m₀ : ℝ) + 1 / N) =
          (((Ord x y : ℤ) : ℝ) + N * t - (N * m₀ + 1)) / N := by
        field_simp
      rw [this]
      exact div_nonneg (by linarith) hNr.le
    have hπ : (0 : ℝ) ≤ 2 * Real.pi := by positivity
    have h2 : 2 * Real.pi * ((m₀ : ℝ) + 1 / (N : ℝ)) ≤
        2 * Real.pi * (((Ord x y : ℤ) : ℝ) / (N : ℝ) + (t : ℝ)) := mul_le_mul_of_nonneg_left hkey hπ
    exact mul_le_mul_of_nonneg_right (neg_le_neg h2) hτ

end S_ModularCurve_SiegelUnit_exists_gamma1_peaked_auxiliary_form_twelve_dvd
end P2MW
export P2MW.S_ModularCurve_SiegelUnit_exists_gamma1_peaked_auxiliary_form_twelve_dvd (solution)
