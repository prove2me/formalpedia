-- Prove2me | solution 1 for ModularCurve.exists_powerSeries_map_eq_ffEquiv_symm_of_placeOfPoint_eq_cuspInftyFull
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/1b4c40a3-2364-5d9f-ba0c-f0ee8c46688e

import Definitions.Def_ModularCurve_QAdicPlace
import Definitions.Def_AlgebraicCurve_CurveModel
import Theorems.Thm_ModularCurve_order_ffEquiv_symm_nonneg_of_placeOfPoint_eq_cuspInftyFull
import Theorems.Thm_ModularCurve_coeff_zero_ffEquiv_symm_eq_zero_of_mem_maximalIdeal_of_placeOfPoint_eq_cuspInftyFull
import Theorems.Thm_RingHom_exists_powerSeries_map_eq_and_constantCoeff_eq_of_retraction_of_ker_le_span_sup_sq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_powerSeries_map_eq_ffEquiv_symm_of_placeOfPoint_eq_cuspInftyFull

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry

namespace LaurentSeries
p2m_open "LaurentSeries"

variable {A L : Type*} [CommRing A] [CommRing L]

def truncToPowerSeries (x : LaurentSeries L) : PowerSeries L := PowerSeries.mk fun n => x.coeff n

@[scoped simp] theorem coeff_truncToPowerSeries (x : LaurentSeries L) (n : ℕ) :
    PowerSeries.coeff n (truncToPowerSeries x) = x.coeff n := by
  rw [truncToPowerSeries, PowerSeries.coeff_mk]

theorem ofPowerSeries_truncToPowerSeries {x : LaurentSeries L} (hx : 0 ≤ x.order) :
    HahnSeries.ofPowerSeries ℤ L (truncToPowerSeries x) = x := by
  ext k
  rcases le_or_gt 0 k with hk | hk
  · lift k to ℕ using hk
    rw [HahnSeries.ofPowerSeries_apply_coeff, coeff_truncToPowerSeries]
  · rw [HahnSeries.ofPowerSeries_apply, HahnSeries.embDomain_notin_range]
    · by_cases hx0 : x = 0
      · rw [hx0]; rfl
      · exact (HahnSeries.coeff_eq_zero_of_lt_order (lt_of_lt_of_le hk hx)).symm
    · rintro ⟨n, hn⟩
      simp only [Nat.castOrderEmbedding_apply] at hn
      omega

private noncomputable def _root_.RingHom.codRestrictPowerSeries (f : A →+* LaurentSeries L) (hf : ∀ a, 0 ≤ (f a).order) :
    A →+* PowerSeries L where
  toFun a := truncToPowerSeries (f a)
  map_one' := by
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := L)
    rw [ofPowerSeries_truncToPowerSeries (hf 1), map_one, map_one]
  map_mul' a b := by
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := L)
    rw [ofPowerSeries_truncToPowerSeries (hf (a * b)), map_mul, map_mul,
      ofPowerSeries_truncToPowerSeries (hf a), ofPowerSeries_truncToPowerSeries (hf b)]
  map_zero' := by
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := L)
    rw [ofPowerSeries_truncToPowerSeries (hf 0), map_zero, map_zero]
  map_add' a b := by
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := L)
    rw [ofPowerSeries_truncToPowerSeries (hf (a + b)), map_add, map_add,
      ofPowerSeries_truncToPowerSeries (hf a), ofPowerSeries_truncToPowerSeries (hf b)]

p2m_alias "P2MW.S_ModularCurve_exists_powerSeries_map_eq_ffEquiv_symm_of_placeOfPoint_eq_cuspInftyFull.RingHom.codRestrictPowerSeries" "RingHom.codRestrictPowerSeries"
private theorem _root_.RingHom.ofPowerSeries_codRestrictPowerSeries (f : A →+* LaurentSeries L) (hf : ∀ a, 0 ≤ (f a).order) (a : A) :
    HahnSeries.ofPowerSeries ℤ L (f.codRestrictPowerSeries hf a) = f a :=
  ofPowerSeries_truncToPowerSeries (hf a)

p2m_alias "P2MW.S_ModularCurve_exists_powerSeries_map_eq_ffEquiv_symm_of_placeOfPoint_eq_cuspInftyFull.RingHom.ofPowerSeries_codRestrictPowerSeries" "RingHom.ofPowerSeries_codRestrictPowerSeries"
@[scoped simp] private theorem _root_.RingHom.coeff_codRestrictPowerSeries (f : A →+* LaurentSeries L) (hf : ∀ a, 0 ≤ (f a).order)
    (a : A) (n : ℕ) : PowerSeries.coeff n (f.codRestrictPowerSeries hf a) = (f a).coeff n :=
  coeff_truncToPowerSeries _ _

p2m_alias "P2MW.S_ModularCurve_exists_powerSeries_map_eq_ffEquiv_symm_of_placeOfPoint_eq_cuspInftyFull.RingHom.coeff_codRestrictPowerSeries" "RingHom.coeff_codRestrictPowerSeries"
p2m_reactivate "P2MW.S_ModularCurve_exists_powerSeries_map_eq_ffEquiv_symm_of_placeOfPoint_eq_cuspInftyFull.LaurentSeries.RingHom"
end LaurentSeries
p2m_reactivate "P2MW.S_ModularCurve_exists_powerSeries_map_eq_ffEquiv_symm_of_placeOfPoint_eq_cuspInftyFull.LaurentSeries.RingHom P2MW.S_ModularCurve_exists_powerSeries_map_eq_ffEquiv_symm_of_placeOfPoint_eq_cuspInftyFull.LaurentSeries"

namespace ModularCurve
p2m_export "ModularCurve" "cuspInftyFull modularFunctionFieldFull order_ffEquiv_symm_nonneg_of_placeOfPoint_eq_cuspInftyFull coeff_zero_ffEquiv_symm_eq_zero_of_mem_maximalIdeal_of_placeOfPoint_eq_cuspInftyFull"
p2m_open "ModularCurve"
namespace QExpFun

def qexp {p : ℕ} (M : AlgebraicCurve.CurveModel ℚ ↥(ModularCurve.modularFunctionFieldFull p))
    (x : closedPoints M.C) : M.C.presheaf.stalk x.1 →+* LaurentSeries ℚ :=
  ((SubringClass.subtype (ModularCurve.modularFunctionFieldFull p)).comp M.ffEquiv.symm.toRingHom).comp
    (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField)

theorem qexp_apply {p : ℕ} (M : AlgebraicCurve.CurveModel ℚ ↥(ModularCurve.modularFunctionFieldFull p))
    (x : closedPoints M.C) (g : M.C.presheaf.stalk x.1) :
    qexp M x g = ((M.ffEquiv.symm (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField g) :
      ↥(ModularCurve.modularFunctionFieldFull p)) : LaurentSeries ℚ) := rfl

theorem main
    {R R' : Type*} [CommRing R] [CommRing R'] [Algebra R ℚ]
    (p : ℕ) [NeZero p]
    (M : AlgebraicCurve.CurveModel ℚ ↥(ModularCurve.modularFunctionFieldFull p))
    (x : closedPoints M.C) (hx : M.placeOfPoint x = ModularCurve.cuspInftyFull p)
    (ι : R →+* R') (π : R' →+* R) (hπ : π.comp ι = RingHom.id R)
    (t : R') (ht : π t = 0) (hcot : RingHom.ker π ≤ Ideal.span {t} ⊔ RingHom.ker π ^ 2)
    (route : R' →+* M.C.presheaf.stalk x.1)
    (hι : ∀ r : R, ((M.ffEquiv.symm (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField (route (ι r))) :
        ↥(ModularCurve.modularFunctionFieldFull p)) : LaurentSeries ℚ) = HahnSeries.C (algebraMap R ℚ r))
    (hI : ∀ i ∈ RingHom.ker π, route i ∈ IsLocalRing.maximalIdeal (M.C.presheaf.stalk x.1))
    (u : PowerSeries R)
    (hu : ((M.ffEquiv.symm (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField (route t)) :
        ↥(ModularCurve.modularFunctionFieldFull p)) : LaurentSeries ℚ) =
      HahnSeries.ofPowerSeries ℤ ℚ (u.map (algebraMap R ℚ)))
    (z : R') :
    ∃ P : PowerSeries R,
      ((M.ffEquiv.symm (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField (route z)) :
          ↥(ModularCurve.modularFunctionFieldFull p)) : LaurentSeries ℚ) =
        HahnSeries.ofPowerSeries ℤ ℚ (P.map (algebraMap R ℚ)) ∧
      PowerSeries.constantCoeff P = π z := by
  set f : R' →+* LaurentSeries ℚ := (qexp M x).comp route with hf
  have hfz : ∀ a, f a = ((M.ffEquiv.symm (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField (route a)) :
      ↥(ModularCurve.modularFunctionFieldFull p)) : LaurentSeries ℚ) := fun a => rfl
  have h0 : ∀ a, 0 ≤ (f a).order := fun a =>
    ModularCurve.order_ffEquiv_symm_nonneg_of_placeOfPoint_eq_cuspInftyFull p M x hx (route a)
  set e : R' →+* PowerSeries ℚ := f.codRestrictPowerSeries h0 with he
  have he' : ∀ a, HahnSeries.ofPowerSeries ℤ ℚ (e a) = f a := fun a =>
    f.ofPowerSeries_codRestrictPowerSeries h0 a
  have hι' : ∀ r : R, e (ι r) = PowerSeries.C (algebraMap R ℚ r) := by
    intro r
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℚ)
    rw [he', hfz, hι, HahnSeries.ofPowerSeries_C]
  have hI' : ∀ i ∈ RingHom.ker π, PowerSeries.constantCoeff (e i) = 0 := by
    intro i hi
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, f.coeff_codRestrictPowerSeries h0, hfz]
    exact ModularCurve.coeff_zero_ffEquiv_symm_eq_zero_of_mem_maximalIdeal_of_placeOfPoint_eq_cuspInftyFull p M x hx
      (route i) (hI i hi)
  have hu' : e t = u.map (algebraMap R ℚ) := by
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℚ)
    rw [he', hfz, hu]
  obtain ⟨P, hP, hc⟩ :=
    RingHom.exists_powerSeries_map_eq_and_constantCoeff_eq_of_retraction_of_ker_le_span_sup_sq
      ι π hπ t ht hcot e hι' hI' u hu' z
  exact ⟨P, by rw [← hfz, ← he', hP], hc⟩

end QExpFun
p2m_reactivate "P2MW.S_ModularCurve_exists_powerSeries_map_eq_ffEquiv_symm_of_placeOfPoint_eq_cuspInftyFull.LaurentSeries.RingHom P2MW.S_ModularCurve_exists_powerSeries_map_eq_ffEquiv_symm_of_placeOfPoint_eq_cuspInftyFull.LaurentSeries"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_exists_powerSeries_map_eq_ffEquiv_symm_of_placeOfPoint_eq_cuspInftyFull.LaurentSeries.RingHom P2MW.S_ModularCurve_exists_powerSeries_map_eq_ffEquiv_symm_of_placeOfPoint_eq_cuspInftyFull.LaurentSeries"
end
p2m_reactivate "P2MW.S_ModularCurve_exists_powerSeries_map_eq_ffEquiv_symm_of_placeOfPoint_eq_cuspInftyFull.LaurentSeries.RingHom P2MW.S_ModularCurve_exists_powerSeries_map_eq_ffEquiv_symm_of_placeOfPoint_eq_cuspInftyFull.LaurentSeries"

theorem solution
    {R R' : Type*} [CommRing R] [CommRing R'] [Algebra R ℚ]
    (p : ℕ) [NeZero p]
    (M : AlgebraicCurve.CurveModel ℚ ↥(ModularCurve.modularFunctionFieldFull p))
    (x : closedPoints M.C) (hx : M.placeOfPoint x = ModularCurve.cuspInftyFull p)
    (ι : R →+* R') (π : R' →+* R) (hπ : π.comp ι = RingHom.id R)
    (t : R') (ht : π t = 0) (hcot : RingHom.ker π ≤ Ideal.span {t} ⊔ RingHom.ker π ^ 2)
    (route : R' →+* M.C.presheaf.stalk x.1)
    (hι : ∀ r : R, ((M.ffEquiv.symm (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField (route (ι r))) :
        ↥(ModularCurve.modularFunctionFieldFull p)) : LaurentSeries ℚ) = HahnSeries.C (algebraMap R ℚ r))
    (hI : ∀ i ∈ RingHom.ker π, route i ∈ IsLocalRing.maximalIdeal (M.C.presheaf.stalk x.1))
    (u : PowerSeries R)
    (hu : ((M.ffEquiv.symm (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField (route t)) :
        ↥(ModularCurve.modularFunctionFieldFull p)) : LaurentSeries ℚ) =
      HahnSeries.ofPowerSeries ℤ ℚ (u.map (algebraMap R ℚ)))
    (z : R') :
    ∃ P : PowerSeries R,
      ((M.ffEquiv.symm (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField (route z)) :
          ↥(ModularCurve.modularFunctionFieldFull p)) : LaurentSeries ℚ) =
        HahnSeries.ofPowerSeries ℤ ℚ (P.map (algebraMap R ℚ)) ∧
      PowerSeries.constantCoeff P = π z :=
  ModularCurve.QExpFun.main p M x hx ι π hπ t ht hcot route hι hI u hu z

end S_ModularCurve_exists_powerSeries_map_eq_ffEquiv_symm_of_placeOfPoint_eq_cuspInftyFull
end P2MW
export P2MW.S_ModularCurve_exists_powerSeries_map_eq_ffEquiv_symm_of_placeOfPoint_eq_cuspInftyFull (solution)
