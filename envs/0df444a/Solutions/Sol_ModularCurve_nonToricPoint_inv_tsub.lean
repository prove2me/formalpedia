-- Prove2me | solution 1 for ModularCurve.nonToricPoint_inv_tsub
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/bb94ed43-8f8b-5f09-b353-cb737af77a09

import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_nonToricPoint_inv_tsub

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

open ModularCurve

namespace P2MKcTateNegSlot

abbrev sw : Fin 2 ≃ Fin 2 := Equiv.swap 0 1

@[scoped simp] theorem sw_zero : sw 0 = 1 := by simp [sw]
@[scoped simp] theorem sw_one : sw 1 = 0 := by simp [sw]

theorem sw_comp_sw : (⇑sw ∘ ⇑sw) = id := by
  funext s; simp [sw, Equiv.swap_apply_self]

theorem coeff_rename_sw (f : MvPowerSeries (Fin 2) ℤ) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (MvPowerSeries.rename sw f) =
      MvPowerSeries.coeff (Finsupp.mapDomain sw e) f := by
  have he : e = Finsupp.embDomain sw.toEmbedding (Finsupp.mapDomain sw e) := by
    rw [Finsupp.embDomain_eq_mapDomain, Equiv.coe_toEmbedding, ← Finsupp.mapDomain_comp, sw_comp_sw,
      Finsupp.mapDomain_id]
  conv_lhs => rw [he]
  exact MvPowerSeries.coeff_embDomain_rename sw.toEmbedding f (Finsupp.mapDomain sw e)

theorem mapDomain_sw_zero (e : Fin 2 →₀ ℕ) : (Finsupp.mapDomain sw e) 0 = e 1 := by
  rw [show (0 : Fin 2) = sw 1 from sw_one.symm, Finsupp.mapDomain_apply sw.injective]

theorem mapDomain_sw_one (e : Fin 2 →₀ ℕ) : (Finsupp.mapDomain sw e) 1 = e 0 := by
  rw [show (1 : Fin 2) = sw 0 from sw_zero.symm, Finsupp.mapDomain_apply sw.injective]

theorem sub_dvd_iff {i j : ℕ} (h : j ≤ i) : (i - j ∣ i) ↔ (i - j ∣ j) := by
  refine ⟨fun hd => ?_, fun hd => ?_⟩
  · have := Nat.dvd_sub hd (dvd_refl (i - j))
    rwa [Nat.sub_sub_self h] at this
  · have := Nat.dvd_add hd (dvd_refl (i - j))
    rwa [Nat.add_sub_cancel' h] at this

def fX (i j : ℕ) : ℤ :=
  if i = j then -2 * ∑ d ∈ j.divisors, (d : ℤ)
  else if j < i then (if i - j ∣ j then ((i - j : ℕ) : ℤ) else 0)
  else (if j - i ∣ j then ((j - i : ℕ) : ℤ) else 0)

def fY (i j : ℕ) : ℤ :=
  if i = j then ∑ d ∈ j.divisors, (d : ℤ)
  else if j < i then (if i - j ∣ j then ((i - j).choose 2 : ℤ) else 0)
  else (if j - i ∣ j then -(((j - i) + 1).choose 2 : ℤ) else 0)

theorem coeff_tateUnivX_eq (e : Fin 2 →₀ ℕ) : MvPowerSeries.coeff e tateUnivX = fX (e 0) (e 1) := by
  rw [tateUnivX_apply]; rfl

theorem coeff_tateUnivY_eq (e : Fin 2 →₀ ℕ) : MvPowerSeries.coeff e tateUnivY = fY (e 0) (e 1) := by
  rw [tateUnivY_apply]; rfl

theorem fX_symm (i j : ℕ) : fX j i = fX i j := by
  rcases lt_trichotomy i j with hij | rfl | hij
  · have h1 : ¬ j = i := hij.ne'
    have h2 : ¬ i = j := hij.ne
    have h3 : ¬ j < i := not_lt.mpr hij.le
    simp only [fX, if_neg h1, if_pos hij, if_neg h2, if_neg h3]
    by_cases hd : j - i ∣ j
    · rw [if_pos ((sub_dvd_iff hij.le).mp hd), if_pos hd]
    · rw [if_neg (fun h => hd ((sub_dvd_iff hij.le).mpr h)), if_neg hd]
  · rfl
  · have h1 : ¬ j = i := hij.ne
    have h2 : ¬ i = j := hij.ne'
    have h3 : ¬ i < j := not_lt.mpr hij.le
    simp only [fX, if_neg h1, if_neg h3, if_neg h2, if_pos hij]
    by_cases hd : i - j ∣ j
    · rw [if_pos ((sub_dvd_iff hij.le).mpr hd), if_pos hd]
    · rw [if_neg (fun h => hd ((sub_dvd_iff hij.le).mp h)), if_neg hd]

theorem cast_choose_two_succ (R : Type*) [CommRing R] (n : ℕ) :
    (((n + 1).choose 2 : ℕ) : R) = ((n.choose 2 : ℕ) : R) + (n : R) := by
  rw [Nat.choose_succ_succ n 1, Nat.choose_one_right]; push_cast; ring

theorem fY_swap (i j : ℕ) : fY j i = -fY i j - fX i j := by
  rcases lt_trichotomy i j with hij | rfl | hij
  · have h1 : ¬ j = i := hij.ne'
    have h2 : ¬ i = j := hij.ne
    have h3 : ¬ j < i := not_lt.mpr hij.le
    simp only [fY, fX, if_neg h1, if_pos hij, if_neg h2, if_neg h3]
    by_cases hd : j - i ∣ j
    · rw [if_pos ((sub_dvd_iff hij.le).mp hd), if_pos hd, if_pos hd, cast_choose_two_succ]; ring
    · rw [if_neg (fun h => hd ((sub_dvd_iff hij.le).mpr h)), if_neg hd, if_neg hd]; ring
  · simp only [fY, fX, if_true]; ring
  · have h1 : ¬ j = i := hij.ne
    have h2 : ¬ i = j := hij.ne'
    have h3 : ¬ i < j := not_lt.mpr hij.le
    simp only [fY, fX, if_neg h1, if_neg h3, if_neg h2, if_pos hij]
    by_cases hd : i - j ∣ j
    · rw [if_pos ((sub_dvd_iff hij.le).mpr hd), if_pos hd, if_pos hd, cast_choose_two_succ]; ring
    · rw [if_neg (fun h => hd ((sub_dvd_iff hij.le).mp h)), if_neg hd, if_neg hd]; ring

theorem rename_sw_tateUnivX : MvPowerSeries.rename sw tateUnivX = tateUnivX := by
  ext e
  rw [coeff_rename_sw, coeff_tateUnivX_eq, coeff_tateUnivX_eq, mapDomain_sw_zero, mapDomain_sw_one]
  exact fX_symm (e 0) (e 1)

theorem rename_sw_tateUnivY : MvPowerSeries.rename sw tateUnivY = -tateUnivY - tateUnivX := by
  ext e
  rw [coeff_rename_sw, map_sub, map_neg, coeff_tateUnivY_eq, coeff_tateUnivY_eq, coeff_tateUnivX_eq,
    mapDomain_sw_zero, mapDomain_sw_one]
  exact fY_swap (e 0) (e 1)

section Slot

variable {K : Type*} [CommRing K] (p : ℕ) (c : Kˣ) (j : ℕ)

theorem slotFamily_inv_tsub (hjp : j ≤ p) :
    slotFamily K p c⁻¹ (p - j) = fun s => slotFamily K p c j (sw s) := by
  funext s
  fin_cases s
  · simp [slotFamily]
  · simp [slotFamily, inv_inv, Nat.sub_sub_self hjp]

theorem hasSubst_slotFamily (hj : 0 < j) (hjp : j < p) : MvPowerSeries.HasSubst (slotFamily K p c j) := by
  refine MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => ?_
  fin_cases s
  · change PowerSeries.constantCoeff (PowerSeries.C (c : K) * PowerSeries.X ^ j) = 0
    simp [PowerSeries.constantCoeff_X, hj.ne']
  · change PowerSeries.constantCoeff (PowerSeries.C ((c⁻¹ : Kˣ) : K) * PowerSeries.X ^ (p - j)) = 0
    have : p - j ≠ 0 := Nat.sub_ne_zero_of_lt hjp
    simp [PowerSeries.constantCoeff_X, this]

theorem subst_comp_sw (a : Fin 2 → PowerSeries K) (ha : MvPowerSeries.HasSubst a) (f : MvPowerSeries (Fin 2) ℤ) :
    MvPowerSeries.subst (fun s => a (sw s)) f = MvPowerSeries.subst a (MvPowerSeries.rename sw f) := by
  rw [MvPowerSeries.rename_eq_subst,
    MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.HasSubst.X_comp _) ha]
  congr 1
  funext s
  simp only [Function.comp_apply, MvPowerSeries.subst_X ha]

theorem slotSubst_inv_tsub (hj : 0 < j) (hjp : j < p) (f : MvPowerSeries (Fin 2) ℤ) :
    slotSubst K p c⁻¹ (p - j) f = slotSubst K p c j (MvPowerSeries.rename sw f) := by
  unfold slotSubst
  rw [slotFamily_inv_tsub p c j hjp.le]
  exact subst_comp_sw (slotFamily K p c j) (hasSubst_slotFamily p c j hj hjp) f

theorem slotSubst_inv_tsub_tateUnivX (hj : 0 < j) (hjp : j < p) :
    slotSubst K p c⁻¹ (p - j) tateUnivX = slotSubst K p c j tateUnivX := by
  rw [slotSubst_inv_tsub p c j hj hjp, rename_sw_tateUnivX]

theorem slotSubst_inv_tsub_tateUnivY (hj : 0 < j) (hjp : j < p) :
    slotSubst K p c⁻¹ (p - j) tateUnivY = -slotSubst K p c j tateUnivY - slotSubst K p c j tateUnivX := by
  rw [slotSubst_inv_tsub p c j hj hjp, rename_sw_tateUnivY]
  unfold slotSubst
  rw [MvPowerSeries.subst_sub (hasSubst_slotFamily p c j hj hjp),
    ← MvPowerSeries.coe_substAlgHom (hasSubst_slotFamily p c j hj hjp), map_neg]

theorem nonToricPoint_inv_tsub (hj : 0 < j) (hjp : j < p) :
    nonToricPoint K p c⁻¹ (p - j) =
      ((nonToricPoint K p c j).1, -(nonToricPoint K p c j).2 - (nonToricPoint K p c j).1) := by
  refine Prod.ext ?_ ?_
  · rw [nonToricPoint_fst, nonToricPoint_fst, slotSubst_inv_tsub_tateUnivX p c j hj hjp]
  · rw [nonToricPoint_snd, nonToricPoint_snd, nonToricPoint_fst, slotSubst_inv_tsub_tateUnivY p c j hj hjp,
      map_sub, map_neg]

end Slot

end P2MKcTateNegSlot
p2m_reactivate "P2MW.S_ModularCurve_nonToricPoint_inv_tsub.P2MKcTateNegSlot"

theorem solution {K : Type*} [CommRing K] (p : ℕ) (c : Kˣ) (j : ℕ)
    (hj : 0 < j) (hjp : j < p) :
    nonToricPoint K p c⁻¹ (p - j) =
      ((nonToricPoint K p c j).1, -(nonToricPoint K p c j).2 - (nonToricPoint K p c j).1) :=
  P2MKcTateNegSlot.nonToricPoint_inv_tsub p c j hj hjp

end
p2m_reactivate "P2MW.S_ModularCurve_nonToricPoint_inv_tsub.P2MKcTateNegSlot"

end S_ModularCurve_nonToricPoint_inv_tsub
end P2MW
export P2MW.S_ModularCurve_nonToricPoint_inv_tsub (solution)
