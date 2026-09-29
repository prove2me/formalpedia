-- Prove2me | solution 1 for ModularCurve.CuspSpace.normalFormCriterion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/a27f70f4-f5f0-5f55-a4a4-6edfa4032b39

import Mathlib
import Definitions.Def_ModularCurve_CuspSpace
import Definitions.Def_ModularCurve_GenusNumerics
import Theorems.Thm_ModularCurve_ratPoint_eq_ratPoint_iff_of_isCoprime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_CuspSpace_normalFormCriterion

set_option autoImplicit false

open Matrix Matrix.SpecialLinearGroup OnePoint CongruenceSubgroup
open scoped MatrixGroups
p2m_open "ModularCurve P2MW.S_ModularCurve_CuspSpace_normalFormCriterion.ModularCurve ModularCurve.CuspSpace P2MW.S_ModularCurve_CuspSpace_normalFormCriterion.ModularCurve.CuspSpace"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "ratPoint mapGL_smul_ratPoint isCoprime_smul_pair CuspSpace CuspSpace.NormalFormCriterion ratPoint_eq_ratPoint_iff_of_isCoprime"
namespace CuspSpace
p2m_export "ModularCurve.CuspSpace" "mk mk_eq_mk_iff mk_smul NormalFormCriterion"
p2m_open "ModularCurve.CuspSpace ModularCurve"

variable {N : ℕ}

lemma dvd_sub_of_smul_eq {e : ℕ} (hN : N ≠ 0) (he : e ∣ N) {A A' ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N)
    (h0 : γ 0 0 * A + γ 0 1 * (e : ℤ) = ε * A')
    (h1 : γ 1 0 * A + γ 1 1 * (e : ℤ) = ε * (e : ℤ)) :
    ((Nat.gcd e (N / e) : ℕ) : ℤ) ∣ A' - A := by
  have he0 : e ≠ 0 := by rintro rfl; exact hN (Nat.eq_zero_of_zero_dvd he)
  have he0' : (e : ℤ) ≠ 0 := by exact_mod_cast he0
  have hε2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num

  have hN10 : (N : ℤ) ∣ γ 1 0 := Gamma0_mem_iff_dvd.mp hγ
  obtain ⟨r₁, hr₁⟩ : (e : ℤ) ∣ γ 1 0 := dvd_trans (by exact_mod_cast he) hN10

  have hem : (e : ℤ) * ((N / e : ℕ) : ℤ) = (N : ℤ) := by exact_mod_cast Nat.mul_div_cancel' he
  have hr₂ : ((N / e : ℕ) : ℤ) ∣ r₁ := by
    have h := hN10
    rw [hr₁, ← hem] at h
    exact (mul_dvd_mul_iff_left he0').mp h

  have hs : γ 1 1 = ε - r₁ * A := by
    have h2 : (e : ℤ) * γ 1 1 = (e : ℤ) * (ε - r₁ * A) := by
      have h := h1
      rw [hr₁] at h
      linear_combination h
    exact mul_left_cancel₀ he0' h2

  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := γ.property
    rwa [Matrix.det_fin_two] at h

  obtain ⟨k, hk⟩ : ((Nat.gcd e (N / e) : ℕ) : ℤ) ∣ r₁ :=
    dvd_trans (by exact_mod_cast Nat.gcd_dvd_right e (N / e)) hr₂
  obtain ⟨l, hl⟩ : ((Nat.gcd e (N / e) : ℕ) : ℤ) ∣ (e : ℤ) := by
    exact_mod_cast Nat.gcd_dvd_left e (N / e)
  refine ⟨ε * A' * A * k + ε * γ 0 1 * l, ?_⟩
  linear_combination (A * r₁ - ε) * h0 + A * hdet + A * γ 0 1 * hr₁ - A * γ 0 0 * hs
    - A' * hε2 + ε * A' * A * hk + ε * γ 0 1 * hl

lemma exists_smul_ratPoint_eq {e : ℕ} (he0 : (e : ℤ) ≠ 0) (a a' q r₁ : ℤ)
    (hq : q * (e : ℤ) = a' - a - r₁ * (a * a')) :
    ∃ γ : SL(2, ℤ), γ 1 0 = (e : ℤ) * r₁ ∧
      mapGL ℚ γ • ratPoint a (e : ℤ) = ratPoint a' (e : ℤ) := by
  obtain ⟨γ, h00, h01, h10, h11⟩ :
      ∃ γ : SL(2, ℤ), γ 0 0 = 1 + r₁ * a' ∧ γ 0 1 = q ∧ γ 1 0 = (e : ℤ) * r₁ ∧
        γ 1 1 = 1 - r₁ * a :=
    ⟨⟨!![1 + r₁ * a', q; (e : ℤ) * r₁, 1 - r₁ * a], by
      rw [Matrix.det_fin_two_of]
      linear_combination (-r₁) * hq⟩, rfl, rfl, rfl, rfl⟩
  refine ⟨γ, h10, ?_⟩
  rw [mapGL_smul_ratPoint (a := a) (c := (e : ℤ)) γ (Or.inr he0), h00, h01, h10, h11,
    show (1 + r₁ * a') * a + q * (e : ℤ) = a' by linear_combination hq,
    show (e : ℤ) * r₁ * a + (1 - r₁ * a) * (e : ℤ) = (e : ℤ) by ring]

end ModularCurve.CuspSpace

end

theorem solution {N : ℕ} (hN : N ≠ 0) :
    ModularCurve.CuspSpace.NormalFormCriterion N := by
  intro a a' e he ha ha'
  have he0 : e ≠ 0 := by rintro rfl; exact hN (Nat.eq_zero_of_zero_dvd he)
  have he0' : (e : ℤ) ≠ 0 := by exact_mod_cast he0
  constructor
  ·
    intro h
    rw [mk_eq_mk_iff] at h
    obtain ⟨γ, hγ, hsmul⟩ := h
    rw [mapGL_smul_ratPoint (a := a') (c := (e : ℤ)) γ (Or.inr he0')] at hsmul
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
    rcases (ratPoint_eq_ratPoint_iff_of_isCoprime (isCoprime_smul_pair γ ha') ha).mp hsmul with
      ⟨h0, h1⟩ | ⟨h0, h1⟩
    · exact dvd_sub_comm.mp (dvd_sub_of_smul_eq (A := a') (A' := a) (ε := 1) hN he
        (Or.inl rfl) hγ (by linear_combination h0) (by linear_combination h1))
    · exact dvd_sub_comm.mp (dvd_sub_of_smul_eq (A := a') (A' := a) (ε := -1) hN he
        (Or.inr rfl) hγ (by linear_combination h0) (by linear_combination h1))
  ·
    intro h
    obtain ⟨w, hw⟩ : ((Nat.gcd e (N / e) : ℕ) : ℤ) ∣ a' - a :=
      (ZMod.intCast_eq_intCast_iff_dvd_sub a a' _).mp h
    obtain ⟨b, c, hbc⟩ := ha.mul_left ha'
    have hgab := Nat.gcd_eq_gcd_ab e (N / e)
    have hem : (e : ℤ) * ((N / e : ℕ) : ℤ) = (N : ℤ) := by exact_mod_cast Nat.mul_div_cancel' he

    have hq : (((Nat.gcd e (N / e) : ℕ) : ℤ) * w * c + Nat.gcdA e (N / e) * w * b * (a * a'))
          * (e : ℤ)
        = a' - a - ((N / e : ℕ) : ℤ) * (Nat.gcdB e (N / e) * w * b) * (a * a') := by
      linear_combination (((Nat.gcd e (N / e) : ℕ) : ℤ) * w) * hbc
        - w * b * (a * a') * hgab - hw
    obtain ⟨γ, hγ10, hγsmul⟩ := exists_smul_ratPoint_eq he0' a a'
      (((Nat.gcd e (N / e) : ℕ) : ℤ) * w * c + Nat.gcdA e (N / e) * w * b * (a * a'))
      (((N / e : ℕ) : ℤ) * (Nat.gcdB e (N / e) * w * b)) hq
    have hγmem : γ ∈ Gamma0 N := by
      refine Gamma0_mem_iff_dvd.mpr ?_
      rw [hγ10]
      exact ⟨Nat.gcdB e (N / e) * w * b, by rw [← hem]; ring⟩
    calc mk N (ratPoint a (e : ℤ))
        = mk N (mapGL ℚ γ • ratPoint a (e : ℤ)) := (mk_smul hγmem _).symm
      _ = mk N (ratPoint a' (e : ℤ)) := by rw [hγsmul]

end S_ModularCurve_CuspSpace_normalFormCriterion
end P2MW
export P2MW.S_ModularCurve_CuspSpace_normalFormCriterion (solution)
