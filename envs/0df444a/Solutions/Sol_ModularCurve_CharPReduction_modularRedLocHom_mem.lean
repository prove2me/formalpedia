-- Prove2me | solution 1 for ModularCurve.CharPReduction.modularRedLocHom_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/d73a00a6-1398-5847-bc70-5b31c5284695

import Definitions.Def_ModularCurve_CharPReduction
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_CharPReduction_modularRedLocHom_mem

p2m_open "ModularCurve P2MW.S_ModularCurve_CharPReduction_modularRedLocHom_mem.ModularCurve ModularCurve.CharPReduction"

set_option autoImplicit false

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "algebraMap_laurentSeries_eq_single jqModC jqNModC jqModC_eq_map_intCast modularFunctionFieldC jqModC_mem jqNModC_mem qExpand_coeff_mul qExpand_coeff_of_not_dvd"
p2m_open "ModularCurve"
namespace CharpSD2

section Modular

variable (N : ℕ) [NeZero N]
variable {L : Type*} [CommRing L]
variable (A : Subring L) {k : Type*} [Field k] (red : A →+* k)

private theorem constSeries_apply (a : A) :
    constSeries A a = HahnSeries.single 0 (a : L) := by
  show algebraMap L (LaurentSeries L) (a : L) = HahnSeries.single 0 (a : L)
  ext m
  rw [HahnSeries.algebraMap_apply', show algebraMap L (PowerSeries L) (a : L)
    = PowerSeries.C (a : L) from by simp, HahnSeries.ofPowerSeries_C]
  rfl

private theorem coeffRed_jqModC :
    coeffRed A red ⟨jqModC L, jqModC_mem_integralCoeffs A⟩ = jqModC k := by
  ext n
  rw [coeffRed_coeff]
  have hL : (⟨(jqModC L).coeff n, jqModC_mem_integralCoeffs A n⟩ : A)
      = (((jqModC ℤ).coeff n : ℤ) : A) := by
    ext
    push_cast
    rw [jqModC_eq_map_intCast, HahnSeries.map_coeff]
    rfl
  rw [hL, map_intCast]
  conv_rhs => rw [jqModC_eq_map_intCast]
  rw [HahnSeries.map_coeff]
  rfl

private theorem coeffRed_jqNModC :
    coeffRed A red ⟨jqNModC L N, jqNModC_mem_integralCoeffs N A⟩ = jqNModC k N := by
  have hqk : ∀ m : ℤ, (jqNModC k N).coeff ((N : ℤ) * m) = (jqModC k).coeff m := fun m => by
    rw [jqNModC, qExpand_coeff_mul]
  have hqk0 : ∀ {n : ℤ}, ¬ ((N : ℕ) : ℤ) ∣ n → (jqNModC k N).coeff n = 0 := fun h => by
    rw [jqNModC]
    exact qExpand_coeff_of_not_dvd _ _ h
  have hqL : ∀ m : ℤ, (jqNModC L N).coeff ((N : ℤ) * m) = (jqModC L).coeff m := fun m => by
    rw [jqNModC, qExpand_coeff_mul]
  have hqL0 : ∀ {n : ℤ}, ¬ ((N : ℕ) : ℤ) ∣ n → (jqNModC L N).coeff n = 0 := fun h => by
    rw [jqNModC]
    exact qExpand_coeff_of_not_dvd _ _ h
  ext n
  rw [coeffRed_coeff]
  by_cases h : ((N : ℕ) : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := h
    have hL : (⟨(jqNModC L N).coeff ((N : ℤ) * m), jqNModC_mem_integralCoeffs N A _⟩ : A)
        = (((jqModC ℤ).coeff m : ℤ) : A) := by
      ext
      push_cast
      rw [hqL, jqModC_eq_map_intCast, HahnSeries.map_coeff]
      rfl
    rw [hL, map_intCast, hqk]
    conv_rhs => rw [jqModC_eq_map_intCast]
    rw [HahnSeries.map_coeff]
    rfl
  · have hL : (⟨(jqNModC L N).coeff n, jqNModC_mem_integralCoeffs N A n⟩ : A) = 0 := by
      ext
      push_cast
      exact hqL0 h
    rw [hL, map_zero, hqk0 h]

private theorem coeffRed_constSeries (a : A) :
    coeffRed A red ⟨constSeries A a, constSeries_mem_integralCoeffs A a⟩
      = algebraMap k (LaurentSeries k) (red a) := by
  ext n
  rw [coeffRed_coeff, algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single]
  by_cases h : n = 0
  · subst h
    have hL : (⟨(constSeries A a).coeff 0, constSeries_mem_integralCoeffs A a 0⟩ : A) = a := by
      ext
      push_cast
      rw [constSeries_apply, HahnSeries.coeff_single]
      simp
    rw [hL, if_pos rfl]
  · have hL : (⟨(constSeries A a).coeff n, constSeries_mem_integralCoeffs A a n⟩ : A) = 0 := by
      ext
      push_cast
      rw [constSeries_apply, HahnSeries.coeff_single]
      simp [h]
    rw [hL, map_zero, if_neg h]

private def redToMffC : Subring (LaurentSeries L) where
  carrier := {x | ∃ h : x ∈ integralCoeffs A,
    coeffRed A red ⟨x, h⟩ ∈ modularFunctionFieldC k N}
  zero_mem' := ⟨(integralCoeffs A).zero_mem, by
    rw [show (⟨(0 : LaurentSeries L), (integralCoeffs A).zero_mem⟩ : integralCoeffs A)
      = 0 from rfl, map_zero]
    exact zero_mem _⟩
  one_mem' := ⟨(integralCoeffs A).one_mem, by
    rw [show (⟨(1 : LaurentSeries L), (integralCoeffs A).one_mem⟩ : integralCoeffs A)
      = 1 from rfl, map_one]
    exact one_mem _⟩
  add_mem' := by
    rintro x y ⟨hx, hxm⟩ ⟨hy, hym⟩
    refine ⟨add_mem hx hy, ?_⟩
    rw [show (⟨x + y, add_mem hx hy⟩ : integralCoeffs A) = ⟨x, hx⟩ + ⟨y, hy⟩ from rfl,
      map_add]
    exact add_mem hxm hym
  neg_mem' := by
    rintro x ⟨hx, hxm⟩
    refine ⟨neg_mem hx, ?_⟩
    rw [show (⟨-x, neg_mem hx⟩ : integralCoeffs A) = -⟨x, hx⟩ from rfl, map_neg]
    exact neg_mem hxm
  mul_mem' := by
    rintro x y ⟨hx, hxm⟩ ⟨hy, hym⟩
    refine ⟨mul_mem hx hy, ?_⟩
    rw [show (⟨x * y, mul_mem hx hy⟩ : integralCoeffs A) = ⟨x, hx⟩ * ⟨y, hy⟩ from rfl,
      map_mul]
    exact mul_mem hxm hym

private theorem modularRing_le_redToMffC : modularRing N A ≤ redToMffC N A red := by
  rw [modularRing, Subring.closure_le]
  rintro x (⟨a, rfl⟩ | rfl | rfl)
  · exact ⟨constSeries_mem_integralCoeffs A a, by
      rw [coeffRed_constSeries]
      exact (modularFunctionFieldC k N).algebraMap_mem _⟩
  · exact ⟨jqModC_mem_integralCoeffs A, by
      rw [coeffRed_jqModC]
      exact jqModC_mem k N⟩
  · exact ⟨jqNModC_mem_integralCoeffs N A, by
      rw [coeffRed_jqNModC]
      exact jqNModC_mem k N⟩

private theorem redRes_mem_mffC (r : modularRing N A) :
    redRes A red (modularRing N A) (modularRing_le_integralCoeffs N A) r
      ∈ modularFunctionFieldC k N := by
  obtain ⟨h𝒜, hmem⟩ := modularRing_le_redToMffC N A red r.2
  exact hmem

private theorem redLoc_mem_mffC
    (f : localizedAtKer A red (modularRing N A) (modularRing_le_integralCoeffs N A)) :
    redLoc f ∈ modularFunctionFieldC k N := by
  obtain ⟨r, s, hs, hfs⟩ := f.2
  have hspec := redLoc_spec f hfs
  have hsne := redRes_ne_zero_of_notMem (A := A) (red := red)
    (R := modularRing N A) (hR := modularRing_le_integralCoeffs N A) hs
  have heq : redLoc f
      = redRes A red (modularRing N A) (modularRing_le_integralCoeffs N A) r
        * (redRes A red (modularRing N A) (modularRing_le_integralCoeffs N A) s)⁻¹ := by
    rw [← hspec, mul_assoc, mul_inv_cancel₀ hsne, mul_one]
  rw [heq]
  exact mul_mem (redRes_mem_mffC N A red r) (inv_mem (redRes_mem_mffC N A red s))

end Modular

end CharpSD2
end ModularCurve

end

theorem solution {L : Type*} [CommRing L] (A : Subring L)
    {k : Type*} [Field k] (red : A →+* k) (N : ℕ) [NeZero N]
    (f : modularLocalized N A red) :
    modularRedLocHom N A red f ∈ modularFunctionFieldC k N:=
  ModularCurve.CharpSD2.redLoc_mem_mffC N A red f

end S_ModularCurve_CharPReduction_modularRedLocHom_mem
end P2MW
export P2MW.S_ModularCurve_CharPReduction_modularRedLocHom_mem (solution)
