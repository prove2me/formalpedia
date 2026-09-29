-- Prove2me | solution 1 for ModularCurve.order_ffEquiv_symm_nonneg_of_placeOfPoint_eq_cuspInftyFull
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/d33d2b4c-0d25-59df-b989-9880e4bbca76

import Definitions.Def_ModularCurve_QAdicPlace
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_order_ffEquiv_symm_nonneg_of_placeOfPoint_eq_cuspInftyFull
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry
namespace ModularCurve
p2m_export "ModularCurve" "qIntegersBar mem_qIntegersBar_iff isUnit_qIntegersBar_iff cuspInftyFull cuspInftyFull_toValuationSubring modularFunctionFieldFull"
p2m_open "ModularCurve"
namespace CuspExpansion

variable (p : ℕ) [NeZero p] (M : AlgebraicCurve.CurveModel ℚ ↥(ModularCurve.modularFunctionFieldFull p))
  (x : closedPoints M.C)

def qexp : M.C.presheaf.stalk x.1 →+* LaurentSeries ℚ :=
  ((SubringClass.subtype (ModularCurve.modularFunctionFieldFull p)).comp M.ffEquiv.symm.toRingHom).comp
    (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField)

theorem qexp_apply (g : M.C.presheaf.stalk x.1) :
    qexp p M x g = ((M.ffEquiv.symm (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField g) :
      ↥(ModularCurve.modularFunctionFieldFull p)) : LaurentSeries ℚ) := rfl

variable {p M x}

theorem order_qexp_nonneg (hx : M.placeOfPoint x = ModularCurve.cuspInftyFull p) (g : M.C.presheaf.stalk x.1) :
    0 ≤ (qexp p M x g).order := by
  have hmem : M.ffEquiv.symm (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField g) ∈
      (M.placeOfPoint x).toValuationSubring.toSubring := by
    rw [← M.range_stalk_eq x]
    exact ⟨g, rfl⟩
  rw [hx, ModularCurve.cuspInftyFull_toValuationSubring] at hmem
  exact (ModularCurve.mem_qIntegersBar_iff (L := ℚ) (F := ModularCurve.modularFunctionFieldFull p)).mp hmem

theorem isUnit_of_order_qexp_eq_zero (hx : M.placeOfPoint x = ModularCurve.cuspInftyFull p)
    {g : M.C.presheaf.stalk x.1} (hg0 : qexp p M x g ≠ 0) (horder : (qexp p M x g).order = 0) : IsUnit g := by
  set G : ↥(ModularCurve.modularFunctionFieldFull p) :=
    M.ffEquiv.symm (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField g) with hG
  have hGmem : G ∈ ModularCurve.qIntegersBar ℚ (ModularCurve.modularFunctionFieldFull p) :=
    (ModularCurve.mem_qIntegersBar_iff (L := ℚ)).mpr (order_qexp_nonneg hx g)
  have hGne : G ≠ 0 := fun h => hg0 (by rw [qexp_apply, ← hG, h]; rfl)
  have hunit : IsUnit (⟨G, hGmem⟩ : ModularCurve.qIntegersBar ℚ (ModularCurve.modularFunctionFieldFull p)) :=
    (ModularCurve.isUnit_qIntegersBar_iff (L := ℚ) hGne).mpr horder
  obtain ⟨w, hw⟩ := hunit.exists_right_inv
  have hwmem : (w : ↥(ModularCurve.modularFunctionFieldFull p)) ∈ (M.placeOfPoint x).toValuationSubring.toSubring := by
    rw [hx, ModularCurve.cuspInftyFull_toValuationSubring]
    exact w.2
  rw [← M.range_stalk_eq x] at hwmem
  obtain ⟨h, hh⟩ := hwmem
  have hw' : (G : ↥(ModularCurve.modularFunctionFieldFull p)) * (w : ↥(ModularCurve.modularFunctionFieldFull p)) = 1 := by
    have := congrArg (fun z : ModularCurve.qIntegersBar ℚ (ModularCurve.modularFunctionFieldFull p) =>
      (z : ↥(ModularCurve.modularFunctionFieldFull p))) hw
    simpa using this
  have hh' : M.ffEquiv.symm (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField h) =
      (w : ↥(ModularCurve.modularFunctionFieldFull p)) := hh
  refine isUnit_iff_exists_inv.mpr ⟨h, ?_⟩
  apply FaithfulSMul.algebraMap_injective (M.C.presheaf.stalk x.1) M.C.functionField
  apply M.ffEquiv.symm.injective
  rw [map_mul, map_mul, map_one, map_one, hh', ← hG]
  exact hw'

theorem coeff_zero_qexp_eq_zero_of_mem (hx : M.placeOfPoint x = ModularCurve.cuspInftyFull p)
    {g : M.C.presheaf.stalk x.1} (hg : g ∈ IsLocalRing.maximalIdeal (M.C.presheaf.stalk x.1)) :
    (qexp p M x g).coeff 0 = 0 := by
  by_contra h0
  have hg0 : qexp p M x g ≠ 0 := fun h => h0 (by rw [h]; rfl)
  have horder : (qexp p M x g).order = 0 :=
    le_antisymm (HahnSeries.order_le_of_coeff_ne_zero h0) (order_qexp_nonneg hx g)
  exact (IsLocalRing.mem_maximalIdeal _).mp hg (isUnit_of_order_qexp_eq_zero hx hg0 horder)

theorem coeff_zero_qexp_eq (hx : M.placeOfPoint x = ModularCurve.cuspInftyFull p)
    (ev : M.C.presheaf.stalk x.1 →+* ℚ) (hev : RingHom.ker ev = IsLocalRing.maximalIdeal _)
    (g : M.C.presheaf.stalk x.1) :
    (qexp p M x g).coeff 0 = ev g := by
  set r : ℚ := ev g with hr

  have hden : IsUnit ((r.den : ℕ) : M.C.presheaf.stalk x.1) := by
    by_contra hu
    have hmem : ((r.den : ℕ) : M.C.presheaf.stalk x.1) ∈ IsLocalRing.maximalIdeal _ :=
      (IsLocalRing.mem_maximalIdeal _).mpr hu
    rw [← hev, RingHom.mem_ker, map_natCast] at hmem
    exact r.den_nz (by exact_mod_cast hmem)
  obtain ⟨u, hu⟩ := hden
  set a' : M.C.presheaf.stalk x.1 := (r.num : M.C.presheaf.stalk x.1) * ((u⁻¹ : (M.C.presheaf.stalk x.1)ˣ) : M.C.presheaf.stalk x.1)
    with ha'
  have heva' : ev a' = r := by
    rw [ha', map_mul, map_intCast, map_units_inv, hu, map_natCast]
    rw [← div_eq_mul_inv]
    exact Rat.num_div_den r
  have hqa' : qexp p M x a' = HahnSeries.C (r : ℚ) := by
    rw [ha', map_mul, map_intCast, map_units_inv, hu, map_natCast]
    rw [← div_eq_mul_inv]
    have : (r : ℚ) = (r.num : ℚ) / (r.den : ℚ) := (Rat.num_div_den r).symm
    conv_rhs => rw [this]
    rw [map_div₀, map_intCast, map_natCast]
  have hdiff : g - a' ∈ IsLocalRing.maximalIdeal _ := by
    rw [← hev, RingHom.mem_ker, map_sub, heva', ← hr, sub_self]
  have h0 := coeff_zero_qexp_eq_zero_of_mem hx hdiff
  rw [map_sub, HahnSeries.coeff_sub', Pi.sub_apply, sub_eq_zero] at h0
  rw [h0, hqa', HahnSeries.C_apply, HahnSeries.coeff_single_same]

end CuspExpansion
end ModularCurve
end

theorem solution
    (p : ℕ) [NeZero p]
    (M : AlgebraicCurve.CurveModel ℚ ↥(ModularCurve.modularFunctionFieldFull p))
    (x : closedPoints M.C) (hx : M.placeOfPoint x = ModularCurve.cuspInftyFull p)
    (g : M.C.presheaf.stalk x.1) :
    0 ≤ (((M.ffEquiv.symm (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField g) :
        ↥(ModularCurve.modularFunctionFieldFull p)) : LaurentSeries ℚ)).order :=
  ModularCurve.CuspExpansion.order_qexp_nonneg hx g

end S_ModularCurve_order_ffEquiv_symm_nonneg_of_placeOfPoint_eq_cuspInftyFull
end P2MW
export P2MW.S_ModularCurve_order_ffEquiv_symm_nonneg_of_placeOfPoint_eq_cuspInftyFull (solution)
