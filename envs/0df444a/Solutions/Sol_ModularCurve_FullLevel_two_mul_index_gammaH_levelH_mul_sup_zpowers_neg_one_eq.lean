-- Prove2me | solution 1 for ModularCurve.FullLevel.two_mul_index_gammaH_levelH_mul_sup_zpowers_neg_one_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/110e4238-bb01-58e5-bae8-1754dd4c9ef5

import Theorems.Thm_CohCarrier_index_gammaH_eq_index_gamma0_mul_index
import Theorems.Thm_ModularCurve_Gamma0_index
import Theorems.Thm_ModularCurve_dedekindPsi_mul_of_coprime
import Theorems.Thm_ModularCurve_dedekindPsi_prime_pow
import Theorems.Thm_Matrix_SpecialLinearGroup_mem_sup_zpowers_neg_one_iff
import Mathlib
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_two_mul_index_gammaH_levelH_mul_sup_zpowers_neg_one_eq
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ"

set_option autoImplicit false

open ModularCurve ModularCurve.FullLevel CongruenceSubgroup
open scoped MatrixGroups

theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 3 ≤ q) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : 3 ≤ ℓ) (hℓq : ℓ ≠ q)
    (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M') (hℓM' : ¬ ℓ ∣ M') :
    2 * (CohCarrier.GammaH ((q * ℓ) ^ 2 * M') (levelH (q * ℓ) M') ⊔
        Subgroup.zpowers (-1 : SL(2, ℤ))).index =
      q * (q ^ 2 - 1) * (ℓ * (ℓ ^ 2 - 1)) * dedekindPsi M' := by
  have hqp : q.Prime := Fact.out
  have hℓp : ℓ.Prime := Fact.out
  haveI hn0 : NeZero (q * ℓ) := ⟨(Nat.mul_pos hqp.pos hℓp.pos).ne'⟩
  haveI hN0 : NeZero ((q * ℓ) ^ 2 * M') :=
    ⟨(Nat.mul_pos (pow_pos (Nat.mul_pos hqp.pos hℓp.pos) 2) (Nat.pos_of_ne_zero (NeZero.ne M'))).ne'⟩
  set Γ : Subgroup SL(2, ℤ) := CohCarrier.GammaH ((q * ℓ) ^ 2 * M') (levelH (q * ℓ) M') with hΓ
  set Z : Subgroup SL(2, ℤ) := Subgroup.zpowers (-1 : SL(2, ℤ)) with hZ

  have hneg : (-1 : SL(2, ℤ)) ∉ Γ := by
    intro h
    rw [hΓ, CohCarrier.mem_GammaH_iff] at h
    obtain ⟨h0, hH⟩ := h
    rw [mem_levelH_iff] at hH
    have hval := congrArg (fun u : (ZMod (q * ℓ))ˣ => (u : ZMod (q * ℓ))) hH
    simp only [ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, CohCarrier.val_gamma0Units,
      Units.val_one] at hval
    have h11 : Gamma0Map ((q * ℓ) ^ 2 * M') ⟨-1, h0⟩ = -1 := by
      show (((((-1 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ)) : ZMod ((q * ℓ) ^ 2 * M')) = -1
      simp
    rw [h11, map_neg, map_one] at hval
    have h2 : ((2 : ℕ) : ZMod (q * ℓ)) = 0 := by
      have : (1 : ZMod (q * ℓ)) + 1 = 0 := by
        nth_rewrite 1 [← hval]; exact neg_add_cancel 1
      exact_mod_cast this
    rw [ZMod.natCast_eq_zero_iff] at h2
    have := Nat.le_of_dvd two_pos h2
    nlinarith

  have hrel : Γ.relIndex (Γ ⊔ Z) = 2 := by
    rw [Subgroup.relIndex_eq_two_iff]
    refine ⟨-1, Subgroup.mem_sup_right (Subgroup.mem_zpowers _), ?_⟩
    intro b hb
    have hb' : b ∈ Γ ∨ -b ∈ Γ :=
      (Matrix.SpecialLinearGroup.mem_sup_zpowers_neg_one_iff Γ b).mp hb
    have hnot : ¬ (b ∈ Γ ∧ -b ∈ Γ) := by
      rintro ⟨h1, h2⟩
      apply hneg
      have := Γ.mul_mem (Γ.inv_mem h1) h2
      rwa [mul_neg, inv_mul_cancel] at this
    rw [mul_neg_one]
    rcases hb' with h | h
    · exact Or.inr ⟨h, fun h' => hnot ⟨h, h'⟩⟩
    · exact Or.inl ⟨h, fun h' => hnot ⟨h', h⟩⟩
  have hidx : 2 * (Γ ⊔ Z).index = Γ.index := by
    have h := Subgroup.relIndex_mul_index (le_sup_left : Γ ≤ Γ ⊔ Z)
    rw [hrel] at h
    exact h
  rw [hidx, hΓ, CohCarrier.index_gammaH_eq_index_gamma0_mul_index, ModularCurve.Gamma0_index]

  have hH : (levelH (q * ℓ) M').index = Nat.totient (q * ℓ) := by
    rw [levelH, Subgroup.index_ker, MonoidHom.range_eq_top.mpr (ZMod.unitsMap_surjective _),
      Subgroup.card_top, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  rw [hH]

  have hcopqℓ : Nat.Coprime q ℓ := (Nat.coprime_primes hqp hℓp).mpr hℓq.symm
  have hcopqM : Nat.Coprime q M' := (Nat.Prime.coprime_iff_not_dvd hqp).mpr hqM'
  have hcopℓM : Nat.Coprime ℓ M' := (Nat.Prime.coprime_iff_not_dvd hℓp).mpr hℓM'
  have hsplit : (q * ℓ) ^ 2 * M' = q ^ 2 * (ℓ ^ 2 * M') := by ring
  rw [hsplit, ModularCurve.dedekindPsi_mul_of_coprime _ _
      ((hcopqℓ.pow 2 2).mul_right (hcopqM.pow_left 2)),
    ModularCurve.dedekindPsi_mul_of_coprime _ _ (hcopℓM.pow_left 2),
    ModularCurve.dedekindPsi_prime_pow q 2 hqp two_ne_zero,
    ModularCurve.dedekindPsi_prime_pow ℓ 2 hℓp two_ne_zero,
    Nat.totient_mul hcopqℓ, Nat.totient_prime hqp, Nat.totient_prime hℓp]
  have key : ∀ n : ℕ, 1 ≤ n → (n ^ 2 + n ^ (2 - 1)) * (n - 1) = n * (n ^ 2 - 1) := by
    intro n hn
    obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le' hn
    have : (a + 1) ^ 2 - 1 = a ^ 2 + 2 * a := Nat.sub_eq_of_eq_add (by ring)
    rw [this, Nat.add_sub_cancel]
    ring
  have kq := key q hqp.one_le
  have kℓ := key ℓ hℓp.one_le
  calc (q ^ 2 + q ^ (2 - 1)) * ((ℓ ^ 2 + ℓ ^ (2 - 1)) * dedekindPsi M') * ((q - 1) * (ℓ - 1))
      = ((q ^ 2 + q ^ (2 - 1)) * (q - 1)) * ((ℓ ^ 2 + ℓ ^ (2 - 1)) * (ℓ - 1)) * dedekindPsi M' := by ring
    _ = q * (q ^ 2 - 1) * (ℓ * (ℓ ^ 2 - 1)) * dedekindPsi M' := by rw [kq, kℓ]

end S_ModularCurve_FullLevel_two_mul_index_gammaH_levelH_mul_sup_zpowers_neg_one_eq
end P2MW
export P2MW.S_ModularCurve_FullLevel_two_mul_index_gammaH_levelH_mul_sup_zpowers_neg_one_eq (solution)
