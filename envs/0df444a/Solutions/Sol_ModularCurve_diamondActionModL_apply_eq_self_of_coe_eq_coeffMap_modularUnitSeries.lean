-- Prove2me | solution 1 for ModularCurve.diamondActionModL_apply_eq_self_of_coe_eq_coeffMap_modularUnitSeries
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/9d369981-052b-5af5-a987-f539f9ea405e

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_XHDiamondModL
import Theorems.Thm_ModularCurve_exists_natDegree_eq_sub_one_and_modularUnit_intCast_eq_aeval_jqModC_of_charP
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_IsDiamondPullbackModL_apply_eq_self_of_coe_mem_qExpFunctionFieldC_gamma0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_diamondActionModL_apply_eq_self_of_coe_eq_coeffMap_modularUnitSeries

set_option autoImplicit false

open AlgebraicCurve ModularCurve
open scoped MatrixGroups

namespace DiamondInvT5

private theorem desc
    (k : Type*) [Field k] (q : ℕ) [Fact q.Prime] [CharP k q] :
    ∃ G : Polynomial k, G.natDegree = q - 1 ∧
      HahnSeries.single (1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ k
          (ModularCurve.dedekindEtaUnit.map (Int.castRingHom k)) *
        (ModularCurve.qExpand k q (HahnSeries.single (1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ k
          (ModularCurve.dedekindEtaUnit.map (Int.castRingHom k))))⁻¹
        = Polynomial.aeval (ModularCurve.jqModC k) G := by
  exact ModularCurve.exists_natDegree_eq_sub_one_and_modularUnit_intCast_eq_aeval_jqModC_of_charP k q

section UnitForms
section AnyRing

variable (R : Type*) [CommRing R] (q : ℕ) [NeZero q]

private noncomputable def unitForm : LaurentSeries R :=
  HahnSeries.single (1 : ℤ) 1 *
      HahnSeries.ofPowerSeries ℤ R (dedekindEtaUnit.map (Int.castRingHom R)) *
    (HahnSeries.single (-(q : ℤ)) 1 *
      qExpand R q (HahnSeries.ofPowerSeries ℤ R (dedekindEtaUnitInv.map (Int.castRingHom R))))

variable {R}

private theorem coeffMap_ofPowerSeries' {S : Type*} [CommRing S] (f : R →+* S) (p : PowerSeries R) :
    coeffMap f (HahnSeries.ofPowerSeries ℤ R p) = HahnSeries.ofPowerSeries ℤ S (p.map f) := by
  ext k
  rw [coeffMap_coeff]
  rcases le_or_gt 0 k with hk | hk
  · lift k to ℕ using hk
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff,
      PowerSeries.coeff_map]
  · rw [ofPowerSeries_coeff_of_neg _ hk, ofPowerSeries_coeff_of_neg _ hk, map_zero]

private theorem coeffMap_unitForm {S : Type*} [CommRing S] (f : R →+* S) :
    coeffMap f (unitForm R q) = unitForm S q := by
  have h1 : f.comp (Int.castRingHom R) = Int.castRingHom S := RingHom.ext_int _ _
  simp only [unitForm, map_mul, coeffMap_single, map_one, coeffMap_ofPowerSeries',
    coeffSemilinearAut.coeffMap_qExpand]
  rw [← RingHom.comp_apply (PowerSeries.map f), ← PowerSeries.map_comp, h1,
    ← RingHom.comp_apply (PowerSeries.map f) (PowerSeries.map (Int.castRingHom R)), ← PowerSeries.map_comp, h1]

end AnyRing

section AnyField

variable (K : Type*) [Field K] (q : ℕ) [NeZero q]

private theorem eta_ne_zero :
    HahnSeries.ofPowerSeries ℤ K (dedekindEtaUnit.map (Int.castRingHom K)) ≠ 0 := by
  intro h
  have h0 := congrArg (fun s : LaurentSeries K => s.coeff 0) h
  simp only [HahnSeries.coeff_zero] at h0
  rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff] at h0
  simp [PowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_dedekindEtaUnit] at h0

private theorem unitForm_eq_field :
    unitForm K q =
      HahnSeries.single (1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ K
          (dedekindEtaUnit.map (Int.castRingHom K)) *
        (qExpand K q (HahnSeries.single (1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ K
          (dedekindEtaUnit.map (Int.castRingHom K))))⁻¹ := by
  have hne : qExpand K q (HahnSeries.single (1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ K
      (dedekindEtaUnit.map (Int.castRingHom K))) ≠ 0 := by
    intro h
    rw [← map_zero (qExpand K q)] at h
    exact mul_ne_zero (HahnSeries.single_ne_zero one_ne_zero) (eta_ne_zero K) (qExpand_injective q h)
  rw [eq_mul_inv_iff_mul_eq₀ hne, unitForm, map_mul, qExpand_single, mul_one]
  have hU : (HahnSeries.ofPowerSeries ℤ K (dedekindEtaUnitInv.map (Int.castRingHom K))) *
      HahnSeries.ofPowerSeries ℤ K (dedekindEtaUnit.map (Int.castRingHom K)) = 1 := by
    rw [← map_mul, ← map_mul (PowerSeries.map (Int.castRingHom K)), mul_comm dedekindEtaUnitInv,
      dedekindEtaUnit_mul_inv, map_one, map_one]
  have hS : (HahnSeries.single (-(q : ℤ)) (1 : K)) * HahnSeries.single ((q : ℤ)) (1 : K) = 1 := by
    rw [HahnSeries.single_mul_single, neg_add_cancel, one_mul, HahnSeries.single_zero_one]
  calc HahnSeries.single (1 : ℤ) (1 : K) * HahnSeries.ofPowerSeries ℤ K (dedekindEtaUnit.map (Int.castRingHom K)) *
        (HahnSeries.single (-(q : ℤ)) 1 * qExpand K q (HahnSeries.ofPowerSeries ℤ K (dedekindEtaUnitInv.map (Int.castRingHom K)))) *
        (HahnSeries.single ((q : ℤ)) 1 * qExpand K q (HahnSeries.ofPowerSeries ℤ K (dedekindEtaUnit.map (Int.castRingHom K))))
      = HahnSeries.single (1 : ℤ) (1 : K) * HahnSeries.ofPowerSeries ℤ K (dedekindEtaUnit.map (Int.castRingHom K)) *
        ((HahnSeries.single (-(q : ℤ)) 1 * HahnSeries.single ((q : ℤ)) 1) *
          qExpand K q (HahnSeries.ofPowerSeries ℤ K (dedekindEtaUnitInv.map (Int.castRingHom K)) *
            HahnSeries.ofPowerSeries ℤ K (dedekindEtaUnit.map (Int.castRingHom K)))) := by
          rw [map_mul]; ring
    _ = _ := by rw [hS, hU, map_one (qExpand K q)]; ring

end AnyField

section Rational

variable (q : ℕ) [NeZero q]

private theorem modularUnitSeries_eq_unitForm : modularUnitSeries q = unitForm ℚ q := by
  rw [unitForm_eq_field, modularUnitSeries, deltaSeriesN, deltaSeries, dedekindEtaUnitQ]

variable (L : Type*) [Field L] [Algebra ℚ L]

private theorem coeffEmb_modularUnitSeries : coeffEmb L (modularUnitSeries q) = unitForm L q := by
  rw [modularUnitSeries_eq_unitForm, coeffEmb, coeffMap_unitForm]

end Rational
end UnitForms

private theorem coeffMap_injective_of_injective {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (hf : Function.Injective f) :
    Function.Injective (coeffMap f : LaurentSeries R →+* LaurentSeries S) := by
  intro a b h
  apply HahnSeries.ext
  funext k
  apply hf
  have := congrArg (fun s : LaurentSeries S => s.coeff k) h
  simpa [coeffMap_coeff] using this

private theorem int_lift_eq_unitForm (p : ℕ) [NeZero p] (x : LaurentSeries ℤ)
    (hx : coeffMap (Int.castRingHom ℚ) x = modularUnitSeries p) : x = unitForm ℤ p := by
  apply coeffMap_injective_of_injective (Int.castRingHom ℚ) (RingHom.injective_int (Int.castRingHom ℚ))
  rw [hx, coeffMap_unitForm, modularUnitSeries_eq_unitForm]

theorem coeffMap_int_lift_mem_qExpFunctionFieldC_gamma0
    (p : ℕ) [Fact p.Prime] (κ : Type*) [Field κ] [CharP κ p] (N : ℕ)
    (x : LaurentSeries ℤ)
    (hx : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; coeffMap (Int.castRingHom ℚ) x = modularUnitSeries p) :
    coeffMap (Int.castRingHom κ) x ∈ qExpFunctionFieldC κ (CongruenceSubgroup.Gamma0 N) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hxZ : x = unitForm ℤ p := int_lift_eq_unitForm p x hx
  have hred : coeffMap (Int.castRingHom κ) x = unitForm κ p := by rw [hxZ, coeffMap_unitForm]
  obtain ⟨G, -, hG⟩ := desc κ p
  have hj : jqModC κ ∈ qExpFunctionFieldC κ (CongruenceSubgroup.Gamma0 N) :=
    intFormRatiosC_subset κ _ (ModularCurve.jqModC_mem_intFormRatiosC κ _)
  rw [hred, unitForm_eq_field, hG]
  have h := Polynomial.aeval_algHom_apply (qExpFunctionFieldC κ (CongruenceSubgroup.Gamma0 N)).val
    (⟨jqModC κ, hj⟩ : qExpFunctionFieldC κ (CongruenceSubgroup.Gamma0 N)) G

  have h' : Polynomial.aeval (jqModC κ) G = ((Polynomial.aeval (⟨jqModC κ, hj⟩ : qExpFunctionFieldC κ (CongruenceSubgroup.Gamma0 N)) G :
      qExpFunctionFieldC κ (CongruenceSubgroup.Gamma0 N)) : LaurentSeries κ) := h
  rw [h']
  exact SetLike.coe_mem _

end DiamondInvT5

open DiamondInvT5 in

theorem solution
    (p : ℕ) [Fact p.Prime] (κ : Type*) [Field κ] [CharP κ p] [IsAlgClosed κ]
    (N : ℕ) [NeZero N] (H' : Subgroup (ZMod N)ˣ) (d : CongruenceSubgroup.Gamma0 N)
    (x : LaurentSeries ℤ)
    (hx : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; coeffMap (Int.castRingHom ℚ) x = modularUnitSeries p)
    (g : ↥(qExpFunctionFieldC κ (CohCarrier.GammaH N H'))) (hg : ((g : ↥(qExpFunctionFieldC κ (CohCarrier.GammaH N H'))) : LaurentSeries κ) = coeffMap (Int.castRingHom κ) x) :
    diamondActionModL κ N H' d g = g := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  by_cases h : ∃ ρ : CongruenceSubgroup.Gamma0 N →*
      (↥(qExpFunctionFieldC κ (CohCarrier.GammaH N H')) ≃ₐ[κ] ↥(qExpFunctionFieldC κ (CohCarrier.GammaH N H'))),
      IsDiamondPullbackModL κ N H' ρ
  · have hρ := isDiamondPullbackModL_diamondActionModL h
    exact IsDiamondPullbackModL.apply_eq_self_of_coe_mem_qExpFunctionFieldC_gamma0 κ N _ hρ d g
      (hg ▸ coeffMap_int_lift_mem_qExpFunctionFieldC_gamma0 p κ N x hx)
  · rw [diamondActionModL_of_not h, MonoidHom.one_apply, AlgEquiv.one_apply]

end S_ModularCurve_diamondActionModL_apply_eq_self_of_coe_eq_coeffMap_modularUnitSeries
end P2MW
export P2MW.S_ModularCurve_diamondActionModL_apply_eq_self_of_coe_eq_coeffMap_modularUnitSeries (solution)
