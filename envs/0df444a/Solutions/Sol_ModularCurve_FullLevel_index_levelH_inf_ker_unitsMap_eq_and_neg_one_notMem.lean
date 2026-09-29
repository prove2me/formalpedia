-- Prove2me | solution 1 for ModularCurve.FullLevel.index_levelH_inf_ker_unitsMap_eq_and_neg_one_notMem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/a6319dfa-eee1-55f8-ba48-94f5c212f166

import Mathlib
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_index_levelH_inf_ker_unitsMap_eq_and_neg_one_notMem

set_option autoImplicit false

open ModularCurve ModularCurve.FullLevel
open scoped MatrixGroups

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hcop : Nat.Coprime q M')
    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg3 : 3 ≤ ℓg) (hℓgM' : ℓg ∣ M')
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker) :
    H₁.index = Nat.totient q * (ℓg - 1) ∧ (-1 : (ZMod (q ^ 2 * M'))ˣ) ∉ H₁ := by
  have hqp : q.Prime := Fact.out
  haveI : NeZero (q ^ 2 * M') := ⟨(Nat.mul_pos (pow_pos hqp.pos 2) (Nat.pos_of_ne_zero (NeZero.ne M'))).ne'⟩
  haveI : NeZero ℓg := ⟨hℓg.ne_zero⟩
  haveI : Fact ℓg.Prime := ⟨hℓg⟩
  haveI : NeZero (q * ℓg) := ⟨(Nat.mul_pos hqp.pos hℓg.pos).ne'⟩
  have hqℓ : Nat.Coprime q ℓg := Nat.Coprime.coprime_dvd_right hℓgM' hcop
  have hdq : q ∣ q ^ 2 * M' := dvd_sq_mul q M'
  have hdℓ : ℓg ∣ q ^ 2 * M' := Dvd.dvd.mul_left hℓgM' (q ^ 2)
  have hdqℓ : q * ℓg ∣ q ^ 2 * M' := Nat.Coprime.mul_dvd_of_dvd_of_dvd hqℓ hdq hdℓ
  let f : (ZMod (q ^ 2 * M'))ˣ →* (ZMod q)ˣ × (ZMod ℓg)ˣ := (ZMod.unitsMap hdq).prod (ZMod.unitsMap hdℓ)
  have hf : ∀ u, f u = (ZMod.unitsMap hdq u, ZMod.unitsMap hdℓ u) := fun _ => rfl
  have hker : H₁ = f.ker := by
    rw [hH₁]; ext u
    rw [Subgroup.mem_inf, mem_levelH_iff, MonoidHom.mem_ker, MonoidHom.mem_ker, hf, Prod.mk_eq_one]
  have hsurj : Function.Surjective f := by
    rintro ⟨u, v⟩
    let e : ZMod (q * ℓg) ≃+* ZMod q × ZMod ℓg := ZMod.chineseRemainder hqℓ
    let w : (ZMod (q * ℓg))ˣ := Units.mapEquiv e.symm.toMulEquiv (MulEquiv.prodUnits.symm (u, v))
    obtain ⟨x, hx⟩ := ZMod.unitsMap_surjective hdqℓ w
    refine ⟨x, ?_⟩
    have hpu : ((MulEquiv.prodUnits.symm (u, v) : (ZMod q × ZMod ℓg)ˣ) : ZMod q × ZMod ℓg) = ((u : ZMod q), (v : ZMod ℓg)) := rfl
    have hw : e (w : ZMod (q * ℓg)) = ((u : ZMod q), (v : ZMod ℓg)) := by
      simp [w, hpu]
    have he1 : ∀ z : ZMod (q * ℓg), (e z).1 = (z.cast : ZMod q) := fun z => by simp [e, ZMod.chineseRemainder]
    have he2 : ∀ z : ZMod (q * ℓg), (e z).2 = (z.cast : ZMod ℓg) := fun z => by simp [e, ZMod.chineseRemainder]
    have hw1 : ((w : ZMod (q * ℓg)).cast : ZMod q) = u := by rw [← he1, hw]
    have hw2 : ((w : ZMod (q * ℓg)).cast : ZMod ℓg) = v := by rw [← he2, hw]
    have c1 : ZMod.unitsMap hdq x = u := by
      have hc : ZMod.unitsMap hdq = (ZMod.unitsMap (dvd_mul_right q ℓg)).comp (ZMod.unitsMap hdqℓ) :=
        (ZMod.unitsMap_comp _ _).symm
      rw [hc, MonoidHom.comp_apply, hx]
      ext
      rw [ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, ZMod.castHom_apply, hw1]
    have c2 : ZMod.unitsMap hdℓ x = v := by
      have hc : ZMod.unitsMap hdℓ = (ZMod.unitsMap (dvd_mul_left ℓg q)).comp (ZMod.unitsMap hdqℓ) :=
        (ZMod.unitsMap_comp _ _).symm
      rw [hc, MonoidHom.comp_apply, hx]
      ext
      rw [ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, ZMod.castHom_apply, hw2]
    rw [hf, c1, c2]
  constructor
  · rw [hker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top, Nat.card_prod,
      Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, ZMod.card_units_eq_totient,
      Nat.totient_prime hℓg]
  · intro h
    rw [hker, MonoidHom.mem_ker, hf, Prod.mk_eq_one] at h
    have hval := congrArg (fun u : (ZMod ℓg)ˣ => (u : ZMod ℓg)) h.2
    simp only [ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, Units.val_neg, Units.val_one, map_neg, map_one] at hval
    have h2 : ((2 : ℕ) : ZMod ℓg) = 0 := by
      have : (1 : ZMod ℓg) + 1 = 0 := by
        nth_rewrite 1 [← hval]; exact neg_add_cancel 1
      exact_mod_cast this
    rw [ZMod.natCast_eq_zero_iff] at h2
    have := Nat.le_of_dvd two_pos h2
    omega

end S_ModularCurve_FullLevel_index_levelH_inf_ker_unitsMap_eq_and_neg_one_notMem
end P2MW
export P2MW.S_ModularCurve_FullLevel_index_levelH_inf_ker_unitsMap_eq_and_neg_one_notMem (solution)
