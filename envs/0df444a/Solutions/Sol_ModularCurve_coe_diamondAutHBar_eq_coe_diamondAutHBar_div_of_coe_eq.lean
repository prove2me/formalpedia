-- Prove2me | solution 1 for ModularCurve.coe_diamondAutHBar_eq_coe_diamondAutHBar_div_of_coe_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/6a7b1e41-d62e-5372-bbcc-c2012e8dc7c8

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Theorems.Thm_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH_of_charZero
import Theorems.Thm_ModularCurve_diamondAutHBar_apply_coeffEmb_eq_coeffEmb_ringAut_apply
import Theorems.Thm_ModularCurve_coe_ringAut_gamma0_apply_eq_of_coe_eq_infSubgroup
import Theorems.Thm_ModularCurve_GammaH_le_GammaH_div_infSubgroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_coe_diamondAutHBar_eq_coe_diamondAutHBar_div_of_coe_eq
p2m_attr_erase "simp" "ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply"

set_option autoImplicit false

open scoped MatrixGroups ModularForm
p2m_open "ModularCurve P2MW.S_ModularCurve_coe_diamondAutHBar_eq_coe_diamondAutHBar_div_of_coe_eq.ModularCurve CongruenceSubgroup"

namespace ModularCurve
p2m_export "ModularCurve" "diamondAutHBar xHFunctionField xHFunctionFieldBar qExpFunctionFieldC qExpFunctionFieldC_mono coeffEmb coeffEmb_mem_laurentBaseChange infSubgroup neZero_div exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH_of_charZero diamondAutHBar_apply_coeffEmb_eq_coeffEmb_ringAut_apply coe_ringAut_gamma0_apply_eq_of_coe_eq_infSubgroup GammaH_le_GammaH_div_infSubgroup"
namespace DResBarBody
p2m_open "ModularCurve"

theorem exists_gamma0_apply_eq {M : ℕ} [NeZero M] (d : (ZMod M)ˣ) :
    ∃ γ : Gamma0 M, (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M) = (d : ZMod M) := by
  set a : ℤ := ((d : ZMod M).val : ℤ) with ha
  have hcop : Nat.Coprime (d : ZMod M).val M := ZMod.val_coe_unit_coprime d
  have hg : Int.gcd a (M : ℤ) = 1 := by rw [ha, Int.gcd_natCast_natCast]; exact hcop
  have hbez : a * Int.gcdA a M + (M : ℤ) * Int.gcdB a M = 1 := by
    have h := Int.gcd_eq_gcd_ab a M
    rw [hg] at h
    push_cast at h
    linarith
  let A : Matrix (Fin 2) (Fin 2) ℤ := !![a, -Int.gcdB a M; (M : ℤ), Int.gcdA a M]
  have hdet : A.det = 1 := by
    rw [Matrix.det_fin_two_of]
    linarith
  refine ⟨⟨⟨A, hdet⟩, ?_⟩, ?_⟩
  · rw [Gamma0_mem]
    show (((M : ℤ) : ℤ) : ZMod M) = 0
    simp
  · show ((a : ℤ) : ZMod M) = d
    rw [ha, Int.cast_natCast, ZMod.natCast_zmod_val]

def toRingAutHom {F : Type*} [Field F] {A : Algebra ℚ F} {G : Type*} [Group G] (ρ : G →* (F ≃ₐ[ℚ] F)) : G →* RingAut F where
  toFun g := (ρ g).toRingEquiv
  map_one' := by ext x; simp
  map_mul' g h := by ext x; simp [AlgEquiv.mul_apply, RingAut.mul_apply]

@[scoped simp] theorem toRingAutHom_apply {F : Type*} [Field F] {A : Algebra ℚ F} {G : Type*} [Group G] (ρ : G →* (F ≃ₐ[ℚ] F)) (g : G) (x : F) :
    toRingAutHom ρ g x = ρ g x := rfl

theorem toRingAutHom_eq_one {F : Type*} [Field F] {A : Algebra ℚ F} {G : Type*} [Group G] (ρ : G →* (F ≃ₐ[ℚ] F)) {g : G}
    (h : ρ g = 1) : toRingAutHom ρ g = 1 := by
  ext x
  rw [toRingAutHom_apply, h]
  rfl

end ModularCurve.DResBarBody
p2m_reactivate "P2MW.S_ModularCurve_coe_diamondAutHBar_eq_coe_diamondAutHBar_div_of_coe_eq.ModularCurve P2MW.S_ModularCurve_coe_diamondAutHBar_eq_coe_diamondAutHBar_div_of_coe_eq.ModularCurve.DResBarBody"
p2m_reactivate "P2MW.S_ModularCurve_coe_diamondAutHBar_eq_coe_diamondAutHBar_div_of_coe_eq.ModularCurve"

namespace ModularCurve p2m_export "ModularCurve" "diamondAutHBar xHFunctionField xHFunctionFieldBar qExpFunctionFieldC qExpFunctionFieldC_mono coeffEmb coeffEmb_mem_laurentBaseChange infSubgroup neZero_div exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH_of_charZero diamondAutHBar_apply_coeffEmb_eq_coeffEmb_ringAut_apply coe_ringAut_gamma0_apply_eq_of_coe_eq_infSubgroup GammaH_le_GammaH_div_infSubgroup" namespace DResBarBody end ModularCurve.DResBarBody
p2m_open_scoped "ModularCurve" in
open ModularCurve.DResBarBody in
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem ModularCurve.DResBarBody.coe_level
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (d : (ZMod M)ˣ) (f : ↥(xHFunctionField M H)) (u : ↥(xHFunctionField (M / p) (infSubgroup p M H hpM)))
    (hfu : (f : LaurentSeries ℚ) = (u : LaurentSeries ℚ)) :
    ((diamondAutHBar M H d ⟨coeffEmb (AlgebraicClosure ℚ) (f : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) f.2⟩ : ↥(xHFunctionFieldBar M H)) :
        LaurentSeries (AlgebraicClosure ℚ)) =
      ((diamondAutHBar (M / p) (infSubgroup p M H hpM) (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d)
          ⟨coeffEmb (AlgebraicClosure ℚ) (u : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) u.2⟩ :
          ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) := by

  obtain ⟨ρM₀, hM_H, -, -, hM_slash⟩ :=
    ModularCurve.exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH_of_charZero ℚ M H
  obtain ⟨ρN₀, hN_H, -, -, hN_slash⟩ :=
    ModularCurve.exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH_of_charZero ℚ (M / p) (infSubgroup p M H hpM)
  set ρM := toRingAutHom ρM₀ with hρM
  set ρN := toRingAutHom ρN₀ with hρN

  obtain ⟨γ, hγ⟩ := exists_gamma0_apply_eq d
  have hγN : (γ : SL(2, ℤ)) ∈ Gamma0 (M / p) := by
    rw [Gamma0_mem]
    have h := Gamma0_mem.mp γ.2
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h ⊢
    exact dvd_trans (Int.natCast_dvd_natCast.mpr (Nat.div_dvd_of_dvd hpM)) h
  set γ' : Gamma0 (M / p) := ⟨(γ : SL(2, ℤ)), hγN⟩ with hγ'
  have hγ'd : ((((γ' : SL(2, ℤ)) 0 0 : ℤ)) : ZMod (M / p)) = ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d : (ZMod (M / p))ˣ) : ZMod (M / p)) := by
    rw [ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, ← hγ, ZMod.castHom_apply, ZMod.cast_intCast (Nat.div_dvd_of_dvd hpM)]

  have hFM := ModularCurve.diamondAutHBar_apply_coeffEmb_eq_coeffEmb_ringAut_apply M H ρM
    (fun g hg => toRingAutHom_eq_one ρM₀ (hM_H g hg))
    (fun g k f g' f₁ g₁ pf pg pf₁ pg₁ c hc hf hg hf₁ hg₁ h1 h2 hg0 hg10 =>
      hM_slash g f g' f₁ g₁ c hc hf hg hf₁ hg₁ h1 h2 hg0 hg10)
    d γ hγ f
  have hFN := ModularCurve.diamondAutHBar_apply_coeffEmb_eq_coeffEmb_ringAut_apply (M / p) (infSubgroup p M H hpM) ρN
    (fun g hg => toRingAutHom_eq_one ρN₀ (hN_H g hg))
    (fun g k f g' f₁ g₁ pf pg pf₁ pg₁ c hc hf hg hf₁ hg₁ h1 h2 hg0 hg10 =>
      hN_slash g f g' f₁ g₁ c hc hf hg hf₁ hg₁ h1 h2 hg0 hg10)
    (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d) γ' hγ'd u
  rw [hFM, hFN]
  congr 1

  exact ModularCurve.coe_ringAut_gamma0_apply_eq_of_coe_eq_infSubgroup p M H hpM ρM
    (fun g hg => toRingAutHom_eq_one ρM₀ (hM_H g hg))
    (fun g k f g' f₁ g₁ pf pg pf₁ pg₁ c hc hf hg hf₁ hg₁ h1 h2 hg0 hg10 =>
      hM_slash g f g' f₁ g₁ c hc hf hg hf₁ hg₁ h1 h2 hg0 hg10)
    ρN
    (fun g hg => toRingAutHom_eq_one ρN₀ (hN_H g hg))
    (fun g k f g' f₁ g₁ pf pg pf₁ pg₁ c hc hf hg hf₁ hg₁ h1 h2 hg0 hg10 =>
      hN_slash g f g' f₁ g₁ c hc hf hg hf₁ hg₁ h1 h2 hg0 hg10)
    γ γ' rfl f u hfu

open ModularCurve.DResBarBody in
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (d : (ZMod M)ˣ) (x : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))
    (hxu : (x : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ))) :
    ((diamondAutHBar M H d x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      ((diamondAutHBar (M / p) (infSubgroup p M H hpM) (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d) u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) :
        LaurentSeries (AlgebraicClosure ℚ)) := by
  haveI : NeZero (M / p) := neZero_div p M hpM
  have hsub : CohCarrier.GammaH M H ≤ CohCarrier.GammaH (M / p) (infSubgroup p M H hpM) :=
    ModularCurve.GammaH_le_GammaH_div_infSubgroup p M H hpM
  have hleF : qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) ≤ qExpFunctionFieldC ℚ (CohCarrier.GammaH M H) :=
    qExpFunctionFieldC_mono ℚ hsub
  have hleB : xHFunctionFieldBar (M / p) (infSubgroup p M H hpM) ≤ xHFunctionFieldBar M H := by
    apply IntermediateField.adjoin.mono
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨v, hleF hv, rfl⟩
  suffices key : ∀ (y : LaurentSeries (AlgebraicClosure ℚ)) (hy : y ∈ xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)),
      ((diamondAutHBar M H d ⟨y, hleB hy⟩ : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
        ((diamondAutHBar (M / p) (infSubgroup p M H hpM) (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d) ⟨y, hy⟩ : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) :
          LaurentSeries (AlgebraicClosure ℚ)) by
    have ex : x = ⟨(u : LaurentSeries (AlgebraicClosure ℚ)), hleB u.2⟩ := Subtype.ext hxu
    rw [ex]
    exact key u.1 u.2
  intro y hy
  induction hy using IntermediateField.adjoin_induction with
  | mem y hy =>
      obtain ⟨v, hv, rfl⟩ := hy
      exact coe_level p M H hpM d ⟨v, hleF hv⟩ ⟨v, hv⟩ rfl
  | algebraMap c =>
      have eM : (⟨algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) c,
          hleB (IntermediateField.algebraMap_mem _ c)⟩ : ↥(xHFunctionFieldBar M H)) = algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) c :=
        Subtype.ext rfl
      have eN : (⟨algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) c,
          IntermediateField.algebraMap_mem _ c⟩ : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) = algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) c :=
        Subtype.ext rfl
      rw [eM, eN, AlgEquiv.commutes, AlgEquiv.commutes]
      rfl
  | add y z hy hz ihy ihz =>
      have eM : (⟨y + z, hleB (IntermediateField.add_mem _ hy hz)⟩ : ↥(xHFunctionFieldBar M H)) = ⟨y, hleB hy⟩ + ⟨z, hleB hz⟩ := rfl
      have eN : (⟨y + z, IntermediateField.add_mem _ hy hz⟩ : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) = ⟨y, hy⟩ + ⟨z, hz⟩ := rfl
      rw [eM, eN, map_add, map_add, AddMemClass.coe_add, AddMemClass.coe_add, ihy, ihz]
  | inv y hy ihy =>
      have eM : (⟨y⁻¹, hleB (IntermediateField.inv_mem _ hy)⟩ : ↥(xHFunctionFieldBar M H)) = (⟨y, hleB hy⟩ : ↥(xHFunctionFieldBar M H))⁻¹ := rfl
      have eN : (⟨y⁻¹, IntermediateField.inv_mem _ hy⟩ : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) = (⟨y, hy⟩ : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))⁻¹ := rfl
      rw [eM, eN, map_inv₀, map_inv₀]
      change ((diamondAutHBar M H d ⟨y, hleB hy⟩ : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ))⁻¹ =
        ((diamondAutHBar (M / p) (infSubgroup p M H hpM) (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d) ⟨y, hy⟩ : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) :
          LaurentSeries (AlgebraicClosure ℚ))⁻¹
      rw [ihy]
  | mul y z hy hz ihy ihz =>
      have eM : (⟨y * z, hleB (IntermediateField.mul_mem _ hy hz)⟩ : ↥(xHFunctionFieldBar M H)) = ⟨y, hleB hy⟩ * ⟨z, hleB hz⟩ := rfl
      have eN : (⟨y * z, IntermediateField.mul_mem _ hy hz⟩ : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) = ⟨y, hy⟩ * ⟨z, hz⟩ := rfl
      rw [eM, eN, map_mul, map_mul, MulMemClass.coe_mul, MulMemClass.coe_mul, ihy, ihz]

#print axioms solution

end S_ModularCurve_coe_diamondAutHBar_eq_coe_diamondAutHBar_div_of_coe_eq
end P2MW
export P2MW.S_ModularCurve_coe_diamondAutHBar_eq_coe_diamondAutHBar_div_of_coe_eq (solution)
