-- Prove2me | solution 1 for ModularCurve.LevelModuliPackageAbs.exists_eq_act_mapRing_of_ker_classify_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/6f4b3f8e-a8d8-5f08-8dcf-8292bd4141d3

import Mathlib
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum

import Theorems.Thm_AlgHom_exists_rangeRestrict_factor_of_ker_eq
import Theorems.Thm_ModularCurve_RigidWeierstrassData_exists_eq_act_of_mk_eq_mk
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_LevelModuliPackageAbs_exists_eq_act_mapRing_of_ker_classify_eq

set_option autoImplicit false

open ModularCurve

theorem solution
    (A : Type) [CommRing A] (Rd : ModularCurve.RigidWeierstrassData A)
    (P₀ : LevelModuliPackageAbs A Rd.toLevelModuliDatum)
    (K : Type) [CommRing K] [Algebra A K]
    (x₁ x₂ : Rd.toLevelModuliDatum.Pt K)
    (h : RingHom.ker (P₀.classify x₁).toRingHom = RingHom.ker (P₀.classify x₂).toRingHom)
    (y₁ y₂ : Rd.Raw K)
    (hy₁ : (Quot.mk _ y₁ : Rd.Pt K) = x₁) (hy₂ : (Quot.mk _ y₂ : Rd.Pt K) = x₂) :
    ∃ (w : Rd.Raw ↥(P₀.classify x₁).range) (κ₁ κ₂ : ↥(P₀.classify x₁).range →ₐ[A] K)
      (C₁ C₂ : WeierstrassCurve.VariableChange K),
      Function.Injective κ₁ ∧ Function.Injective κ₂ ∧ (∀ r : ↥(P₀.classify x₁).range, κ₁ r = (r : K)) ∧
      y₁ = Rd.act C₁ (Rd.mapRing κ₁ w) ∧ y₂ = Rd.act C₂ (Rd.mapRing κ₂ w) := by
  obtain ⟨ψ, κ₂, hψs, hκ₂i, hψ1, hψ2⟩ :=
    AlgHom.exists_rangeRestrict_factor_of_ker_eq (P₀.classify x₁) (P₀.classify x₂) h
  let κ₁ : ↥(P₀.classify x₁).range →ₐ[A] K := (P₀.classify x₁).range.val
  let D := Rd.toLevelModuliDatum
  let z : Rd.Pt ↥(P₀.classify x₁).range := D.map ψ P₀.univ
  obtain ⟨w, hw⟩ := Quot.exists_rep z
  have hcomp₁ : κ₁.comp ψ = P₀.classify x₁ := AlgHom.ext fun b => hψ1 b
  have hcomp₂ : κ₂.comp ψ = P₀.classify x₂ := AlgHom.ext fun b => hψ2 b
  have hx₁ : D.map κ₁ z = x₁ := by
    show D.map κ₁ (D.map ψ P₀.univ) = x₁
    rw [← D.map_comp, hcomp₁, P₀.map_classify]
  have hx₂ : D.map κ₂ z = x₂ := by
    show D.map κ₂ (D.map ψ P₀.univ) = x₂
    rw [← D.map_comp, hcomp₂, P₀.map_classify]
  have e₁ : (Quot.mk _ (Rd.mapRing κ₁ w) : Rd.Pt K) = Quot.mk _ y₁ := by
    rw [← Rd.map_mk κ₁ w, hw, hy₁]; exact hx₁
  have e₂ : (Quot.mk _ (Rd.mapRing κ₂ w) : Rd.Pt K) = Quot.mk _ y₂ := by
    rw [← Rd.map_mk κ₂ w, hw, hy₂]; exact hx₂
  obtain ⟨C₁, hC₁⟩ := Rd.exists_eq_act_of_mk_eq_mk (Rd.mapRing κ₁ w) y₁ e₁
  obtain ⟨C₂, hC₂⟩ := Rd.exists_eq_act_of_mk_eq_mk (Rd.mapRing κ₂ w) y₂ e₂
  exact ⟨w, κ₁, κ₂, C₁, C₂, fun a b hab => Subtype.ext hab, hκ₂i, fun r => rfl, hC₁, hC₂⟩

end S_ModularCurve_LevelModuliPackageAbs_exists_eq_act_mapRing_of_ker_classify_eq
end P2MW
export P2MW.S_ModularCurve_LevelModuliPackageAbs_exists_eq_act_mapRing_of_ker_classify_eq (solution)
