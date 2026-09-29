-- Prove2me | solution 1 for ModularCurve.FullLevel.Diamond.two_mul_index_gammaH_levelH_inf_ker_sup_zpowers_neg_one_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/cb2adc7d-1afc-5fbe-9ffc-cd206ad76c47

import Mathlib
import Definitions.Def_ModularCurve_FullLevelJacobian

import Theorems.Thm_CohCarrier_index_gammaH_eq_index_gamma0_mul_index
import Theorems.Thm_ModularCurve_Gamma0_index
import Theorems.Thm_ModularCurve_dedekindPsi_mul_of_coprime
import Theorems.Thm_ModularCurve_dedekindPsi_prime_pow
import Theorems.Thm_Matrix_SpecialLinearGroup_mem_sup_zpowers_neg_one_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_Diamond_two_mul_index_gammaH_levelH_inf_ker_sup_zpowers_neg_one_eq
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ"

set_option autoImplicit false

open ModularCurve ModularCurve.FullLevel CongruenceSubgroup
open scoped MatrixGroups

namespace IndexH1

theorem eq_one_of_cast_eq_one {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) (x : ZMod (a * b))
    (ha : ZMod.castHom (dvd_mul_right a b) (ZMod a) x = 1) (hb : ZMod.castHom (dvd_mul_left b a) (ZMod b) x = 1) :
    x = 1 := by
  haveI : NeZero (a * b) := ⟨Nat.mul_ne_zero (NeZero.ne a) (NeZero.ne b)⟩
  have key : ∀ {c : ℕ} [NeZero c] (hc : c ∣ a * b), ZMod.castHom hc (ZMod c) x = 1 → c ∣ (x - 1).val := by
    intro c _ hc h
    have h0 : ZMod.castHom hc (ZMod c) (x - 1) = 0 := by rw [map_sub, h, map_one, sub_self]
    rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff] at h0
    exact h0
  have hdvd : a * b ∣ (x - 1).val := Nat.Coprime.mul_dvd_of_dvd_of_dvd hab (key _ ha) (key _ hb)
  have hlt : (x - 1).val < a * b := ZMod.val_lt _
  have h0 : (x - 1).val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
  rw [ZMod.val_eq_zero, sub_eq_zero] at h0
  exact h0

end IndexH1

theorem solution
    (q : ℕ) [Fact q.Prime] (ℓg : ℕ) [Fact ℓg.Prime] (hℓg3 : 3 ≤ ℓg)
    (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M') (hℓgM' : ℓg ∣ M') :
    2 * (CohCarrier.GammaH (q ^ 2 * M')
          (levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker) ⊔
        Subgroup.zpowers (-1 : SL(2, ℤ))).index =
      q * (q ^ 2 - 1) * (ℓg - 1) * dedekindPsi M' := by
  have hqp : q.Prime := Fact.out
  have hℓp : ℓg.Prime := Fact.out
  have hℓq : ℓg ≠ q := fun h => hqM' (h ▸ hℓgM')
  haveI : NeZero q := ⟨hqp.ne_zero⟩
  haveI : NeZero ℓg := ⟨hℓp.ne_zero⟩
  haveI hn0 : NeZero (q * ℓg) := ⟨(Nat.mul_pos hqp.pos hℓp.pos).ne'⟩
  haveI hN0 : NeZero (q ^ 2 * M') := ⟨Nat.mul_ne_zero (pow_ne_zero 2 hqp.ne_zero) (NeZero.ne M')⟩
  have hcopqℓ : Nat.Coprime q ℓg := (Nat.coprime_primes hqp hℓp).mpr hℓq.symm
  have hqℓN : q * ℓg ∣ q ^ 2 * M' :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd hcopqℓ (dvd_sq_mul q M') (Dvd.dvd.mul_left hℓgM' (q ^ 2))
  set H : Subgroup (ZMod (q ^ 2 * M'))ˣ :=
    levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker with hHdef
  set Γ : Subgroup SL(2, ℤ) := CohCarrier.GammaH (q ^ 2 * M') H with hΓ
  set Z : Subgroup SL(2, ℤ) := Subgroup.zpowers (-1 : SL(2, ℤ)) with hZ

  have hHker : H = (ZMod.unitsMap hqℓN).ker := by
    ext u
    rw [hHdef, Subgroup.mem_inf, mem_levelH_iff, MonoidHom.mem_ker, MonoidHom.mem_ker]
    constructor
    · rintro ⟨h1, h2⟩
      apply Units.ext
      have e1 : ((ZMod.unitsMap (dvd_sq_mul q M') u : (ZMod q)ˣ) : ZMod q) =
          ZMod.castHom (dvd_mul_right q ℓg) (ZMod q) ((ZMod.unitsMap hqℓN u : (ZMod (q * ℓg))ˣ) : ZMod (q * ℓg)) := by
        rw [show ZMod.unitsMap (dvd_sq_mul q M') = (ZMod.unitsMap (dvd_mul_right q ℓg)).comp (ZMod.unitsMap hqℓN) from
          (ZMod.unitsMap_comp (dvd_mul_right q ℓg) hqℓN).symm]
        simp [ZMod.unitsMap_def]
      have e2 : ((ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2)) u : (ZMod ℓg)ˣ) : ZMod ℓg) =
          ZMod.castHom (dvd_mul_left ℓg q) (ZMod ℓg) ((ZMod.unitsMap hqℓN u : (ZMod (q * ℓg))ˣ) : ZMod (q * ℓg)) := by
        rw [show ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2)) = (ZMod.unitsMap (dvd_mul_left ℓg q)).comp (ZMod.unitsMap hqℓN) from
          (ZMod.unitsMap_comp (dvd_mul_left ℓg q) hqℓN).symm]
        simp [ZMod.unitsMap_def]
      rw [Units.val_one]
      refine IndexH1.eq_one_of_cast_eq_one hcopqℓ _ ?_ ?_
      · rw [← e1, h1, Units.val_one]
      · rw [← e2, h2, Units.val_one]
    · intro h
      constructor
      · have hc : ZMod.unitsMap (dvd_sq_mul q M') = (ZMod.unitsMap (dvd_mul_right q ℓg)).comp (ZMod.unitsMap hqℓN) :=
          (ZMod.unitsMap_comp (dvd_mul_right q ℓg) hqℓN).symm
        rw [hc, MonoidHom.comp_apply, h, map_one]
      · have hc : ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2)) = (ZMod.unitsMap (dvd_mul_left ℓg q)).comp (ZMod.unitsMap hqℓN) :=
          (ZMod.unitsMap_comp (dvd_mul_left ℓg q) hqℓN).symm
        rw [hc, MonoidHom.comp_apply, h, map_one]

  have hneg : (-1 : SL(2, ℤ)) ∉ Γ := by
    intro h
    rw [hΓ, CohCarrier.mem_GammaH_iff] at h
    obtain ⟨h0, hH⟩ := h
    rw [hHdef, Subgroup.mem_inf] at hH
    obtain ⟨-, hH⟩ := hH
    rw [MonoidHom.mem_ker] at hH
    have hval := congrArg (fun u : (ZMod ℓg)ˣ => (u : ZMod ℓg)) hH
    simp only [ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, CohCarrier.val_gamma0Units,
      Units.val_one] at hval
    have h11 : Gamma0Map (q ^ 2 * M') ⟨-1, h0⟩ = -1 := by
      show (((((-1 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ)) : ZMod (q ^ 2 * M')) = -1
      simp
    rw [h11, map_neg, map_one] at hval
    have h2 : ((2 : ℕ) : ZMod ℓg) = 0 := by
      have : (1 : ZMod ℓg) + 1 = 0 := by
        nth_rewrite 1 [← hval]; exact neg_add_cancel 1
      exact_mod_cast this
    rw [ZMod.natCast_eq_zero_iff] at h2
    have := Nat.le_of_dvd two_pos h2
    omega

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

  have hH : H.index = Nat.totient (q * ℓg) := by
    rw [hHker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr (ZMod.unitsMap_surjective _),
      Subgroup.card_top, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  rw [hH]

  have hcopqM : Nat.Coprime q M' := (Nat.Prime.coprime_iff_not_dvd hqp).mpr hqM'
  rw [ModularCurve.dedekindPsi_mul_of_coprime _ _ (hcopqM.pow_left 2),
    ModularCurve.dedekindPsi_prime_pow q 2 hqp two_ne_zero,
    Nat.totient_mul hcopqℓ, Nat.totient_prime hqp, Nat.totient_prime hℓp]
  have key : ∀ n : ℕ, 1 ≤ n → (n ^ 2 + n ^ (2 - 1)) * (n - 1) = n * (n ^ 2 - 1) := by
    intro n hn
    obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le' hn
    have : (a + 1) ^ 2 - 1 = a ^ 2 + 2 * a := Nat.sub_eq_of_eq_add (by ring)
    rw [this, Nat.add_sub_cancel]
    ring
  have kq := key q hqp.one_le
  calc (q ^ 2 + q ^ (2 - 1)) * dedekindPsi M' * ((q - 1) * (ℓg - 1))
      = ((q ^ 2 + q ^ (2 - 1)) * (q - 1)) * (ℓg - 1) * dedekindPsi M' := by ring
    _ = q * (q ^ 2 - 1) * (ℓg - 1) * dedekindPsi M' := by rw [kq]

end S_ModularCurve_FullLevel_Diamond_two_mul_index_gammaH_levelH_inf_ker_sup_zpowers_neg_one_eq
end P2MW
export P2MW.S_ModularCurve_FullLevel_Diamond_two_mul_index_gammaH_levelH_inf_ker_sup_zpowers_neg_one_eq (solution)
