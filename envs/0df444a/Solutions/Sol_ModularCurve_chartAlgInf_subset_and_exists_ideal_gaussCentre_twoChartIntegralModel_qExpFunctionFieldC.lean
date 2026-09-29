-- Prove2me | solution 1 for ModularCurve.chartAlgInf_subset_and_exists_ideal_gaussCentre_twoChartIntegralModel_qExpFunctionFieldC
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/80af1705-6db3-53ac-aa8e-9c55b33d9eef

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_GaloisRep_RatLocalizedAtResidue
import Theorems.Thm_ModularCurve_exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_exists_algHom_chartAlgInf_ratLocalizedAt_apply_eq_coeff_zero
import Theorems.Thm_ModularCurve_coeff_jqModC_neg_one
import Theorems.Thm_GaloisRep_ratLocalizedAt_maximalIdeal_eq_span_natCast
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_chartAlgInf_subset_and_exists_ideal_gaussCentre_twoChartIntegralModel_qExpFunctionFieldC

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open scoped MatrixGroups
p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_chartAlgInf_subset_and_exists_ideal_gaussCentre_twoChartIntegralModel_qExpFunctionFieldC.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "qExpFunctionFieldC jNum constantCoeff_jNum jNumQ constantCoeff_jNumQ ofPowerSeries_coeff_of_neg coeffMap coeffMap_coeff algebraMap_laurentSeries_eq_single jqModC exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC exists_algHom_chartAlgInf_ratLocalizedAt_apply_eq_coeff_zero coeff_jqModC_neg_one"
namespace GaussCentre
p2m_open "ModularCurve"

abbrev Rp (p : ℕ) : Type := ↥(GaloisRep.ratLocalizedAt p)

scoped instance (p : ℕ) [hp : Fact p.Prime] : IsDiscreteValuationRing (Rp p) :=
  GaloisRep.isDiscreteValuationRing_ratLocalizedAt p hp.out

theorem maximalIdeal_eq (p : ℕ) [hp : Fact p.Prime] :
    IsLocalRing.maximalIdeal (Rp p) = Ideal.span {(p : Rp p)} :=
  GaloisRep.ratLocalizedAt.maximalIdeal_eq_span_natCast p hp.out

theorem residue_eq_zero_of_mem (p : ℕ) [hp : Fact p.Prime] {r : Rp p} (hr : r ∈ IsLocalRing.maximalIdeal (Rp p)) :
    GaloisRep.ratLocalizedAtResidue p r = 0 := by
  rw [maximalIdeal_eq, Ideal.mem_span_singleton] at hr
  obtain ⟨s, rfl⟩ := hr
  rw [map_mul, map_natCast, ZMod.natCast_self, zero_mul]

theorem isUnit_of_residue_ne_zero (p : ℕ) [hp : Fact p.Prime] {r : Rp p}
    (hr : GaloisRep.ratLocalizedAtResidue p r ≠ 0) : IsUnit r := by
  by_contra h
  exact hr (residue_eq_zero_of_mem p ((IsLocalRing.mem_maximalIdeal _).mpr h))

theorem exists_eq_mul_of_residue_eq_zero (p : ℕ) [hp : Fact p.Prime] {r : Rp p}
    (hr : GaloisRep.ratLocalizedAtResidue p r = 0) : ∃ s : Rp p, r = p * s := by
  have h : ¬ IsUnit r := fun hu => (hu.map (GaloisRep.ratLocalizedAtResidue p)).ne_zero hr
  have hm : r ∈ IsLocalRing.maximalIdeal (Rp p) := (IsLocalRing.mem_maximalIdeal _).mpr h
  rw [maximalIdeal_eq, Ideal.mem_span_singleton] at hm
  exact hm

abbrev psQ (p : ℕ) (x : PowerSeries (Rp p)) : LaurentSeries ℚ :=
  HahnSeries.ofPowerSeries ℤ ℚ (x.map (GaloisRep.ratLocalizedAt p).subtype)

theorem psQ_injective (p : ℕ) : Function.Injective (psQ p) := fun x y h =>
  PowerSeries.map_injective _ Subtype.coe_injective (HahnSeries.ofPowerSeries_injective h)

theorem subtype_comp_intCast (p : ℕ) :
    (GaloisRep.ratLocalizedAt p).subtype.comp (Int.castRingHom (Rp p)) = Int.castRingHom ℚ :=
  RingHom.ext_int _ _

theorem residue_comp_intCast (p : ℕ) [Fact p.Prime] :
    (GaloisRep.ratLocalizedAtResidue p).comp (Int.castRingHom (Rp p)) = Int.castRingHom (ZMod p) :=
  RingHom.ext_int _ _

theorem jqModC_rat_ne_zero : jqModC ℚ ≠ 0 := by
  intro h
  have := congrArg (fun s : LaurentSeries ℚ => s.coeff (-1)) h
  simp only [coeff_jqModC_neg_one, HahnSeries.coeff_zero] at this
  exact one_ne_zero this

theorem single_one_mul_jqModC :
    HahnSeries.single (1 : ℤ) (1 : ℚ) * jqModC ℚ = HahnSeries.ofPowerSeries ℤ ℚ (jNum.map (Int.castRingHom ℚ)) := by
  rw [jqModC, ← mul_assoc, HahnSeries.single_mul_single, add_neg_cancel, one_mul]
  exact one_mul _

theorem map_map_ps {A B C : Type*} [CommSemiring A] [CommSemiring B] [CommSemiring C] (f : A →+* B) (g : B →+* C)
    (x : PowerSeries A) : (x.map f).map g = x.map (g.comp f) := by
  ext n
  simp only [PowerSeries.coeff_map, RingHom.comp_apply]

theorem psQ_jNum (p : ℕ) : psQ p (jNum.map (Int.castRingHom (Rp p))) = HahnSeries.ofPowerSeries ℤ ℚ (jNum.map (Int.castRingHom ℚ)) := by
  rw [psQ, map_map_ps, subtype_comp_intCast]

theorem psQ_X (p : ℕ) : psQ p PowerSeries.X = HahnSeries.single (1 : ℤ) (1 : ℚ) := by
  rw [psQ, PowerSeries.map_X, HahnSeries.ofPowerSeries_X]

theorem jNum_map_residue_ne_zero (p : ℕ) [Fact p.Prime] :
    (jNum.map (Int.castRingHom (Rp p))).map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 := by
  rw [map_map_ps, residue_comp_intCast]
  intro h
  have := congrArg PowerSeries.constantCoeff h
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff,
    constantCoeff_jNum, map_one, map_zero] at this
  exact one_ne_zero this

theorem coeff_zero_inv_jqModC : ((jqModC ℚ)⁻¹).coeff 0 = 0 := by
  have hu : jNumQ * jNumQ.invOfUnit 1 = 1 := PowerSeries.mul_invOfUnit _ _ (by rw [constantCoeff_jNumQ]; rfl)
  have hj : jqModC ℚ = HahnSeries.single (-1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ ℚ jNumQ := rfl
  have hinv : (jqModC ℚ)⁻¹ = HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.X * jNumQ.invOfUnit 1) := by
    apply inv_eq_of_mul_eq_one_right
    rw [hj, map_mul, HahnSeries.ofPowerSeries_X, mul_mul_mul_comm, HahnSeries.single_mul_single, neg_add_cancel, one_mul,
      ← map_mul, hu, map_one (HahnSeries.ofPowerSeries ℤ ℚ), mul_one]
    rfl
  rw [hinv, show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_zero_X_mul]

abbrev FG (Γ : Subgroup SL(2, ℤ)) : Type := ↥(qExpFunctionFieldC ℚ Γ)

abbrev OO (Γ : Subgroup SL(2, ℤ)) (p : ℕ) (j : FG Γ) [Fact (j ≠ 0)] : Type :=
  ↥(TwoChartIntegralModel.chartAlgInf (Rp p) (FG Γ) j)

abbrev Aj (Γ : Subgroup SL(2, ℤ)) (p : ℕ) (j : FG Γ) : Subalgebra (Rp p) (FG Γ) :=
  Algebra.adjoin (Rp p) ({j⁻¹} : Set (FG Γ))

section Frame

variable (Γ : Subgroup SL(2, ℤ)) (p : ℕ) [hp : Fact p.Prime]
variable (j : FG Γ) [Fact (j ≠ 0)] (hj : (j : LaurentSeries ℚ) = jqModC ℚ)
variable (W₀ : ValuationSubring (FG Γ))
  (hW₀ : ∀ f : FG Γ, f ∈ W₀ ↔
    ∃ a a' : PowerSeries (Rp p), a'.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 ∧
      (f : LaurentSeries ℚ) * psQ p a' = psQ p a)

include hW₀ in

theorem algebraMap_mem (r : Rp p) : algebraMap (Rp p) (FG Γ) r ∈ W₀ := by
  rw [hW₀]
  refine ⟨PowerSeries.C r, 1, by rw [map_one]; exact one_ne_zero, ?_⟩
  rw [psQ, psQ, map_one, map_one, mul_one, PowerSeries.map_C, HahnSeries.ofPowerSeries_C, HahnSeries.C_apply]
  have h1 : ((algebraMap (Rp p) (FG Γ) r : FG Γ) : LaurentSeries ℚ) = HahnSeries.single 0 (r : ℚ) := by
    first
    | exact algebraMap_laurentSeries_eq_single (r : ℚ)
    | rfl
    | (change algebraMap ℚ (LaurentSeries ℚ) (r : ℚ) = _; exact algebraMap_laurentSeries_eq_single ℚ (r : ℚ))
  rw [h1]
  rfl

include hj hW₀ in

theorem inv_j_mem : (j⁻¹ : FG Γ) ∈ W₀ := by
  rw [hW₀]
  refine ⟨PowerSeries.X, jNum.map (Int.castRingHom (Rp p)), jNum_map_residue_ne_zero p, ?_⟩
  rw [psQ_jNum, psQ_X, ← single_one_mul_jqModC, ← hj]
  show ((j : FG Γ) : LaurentSeries ℚ)⁻¹ * (HahnSeries.single 1 1 * (j : LaurentSeries ℚ)) = HahnSeries.single 1 1
  rw [mul_left_comm, inv_mul_cancel₀ (hj ▸ jqModC_rat_ne_zero), mul_one]

include hj hW₀ in

theorem j_mem : (j : FG Γ) ∈ W₀ := by
  rw [hW₀]
  refine ⟨jNum.map (Int.castRingHom (Rp p)), PowerSeries.X, by rw [PowerSeries.map_X]; exact PowerSeries.X_ne_zero, ?_⟩
  rw [psQ_jNum, psQ_X, ← single_one_mul_jqModC, ← hj, mul_comm]

include hj hW₀ in

theorem adjoin_subset (x : FG Γ) (hx : x ∈ Algebra.adjoin (Rp p) ({j⁻¹} : Set (FG Γ))) : x ∈ W₀ := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact inv_j_mem Γ p j hj W₀ hW₀
  | algebraMap r => exact algebraMap_mem Γ p W₀ hW₀ r
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy => exact mul_mem hx hy

include hj hW₀ in

theorem coe_mem (b : OO Γ p j) : (b : FG Γ) ∈ W₀ := by
  have hb : IsIntegral (Algebra.adjoin (Rp p) ({j⁻¹} : Set (FG Γ))) (b : FG Γ) := b.2
  let φ : ↥(Algebra.adjoin (Rp p) ({j⁻¹} : Set (FG Γ))) →+* ↥W₀ :=
    (algebraMap ↥(Algebra.adjoin (Rp p) ({j⁻¹} : Set (FG Γ))) (FG Γ)).codRestrict W₀.toSubring
      (fun x => adjoin_subset Γ p j hj W₀ hW₀ x x.2)
  have hcomp : (algebraMap ↥W₀ (FG Γ)).comp φ = (RingHom.id (FG Γ)).comp (algebraMap _ (FG Γ)) :=
    RingHom.ext fun _ => rfl
  have hint : IsIntegral ↥W₀ (b : FG Γ) := hb.map_of_comp_eq φ (RingHom.id (FG Γ)) hcomp
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥W₀) (K := FG Γ)).mp hint
  rw [← hy]
  exact y.2

def toW₀ : OO Γ p j →+* ↥W₀ :=
  (algebraMap (OO Γ p j) (FG Γ)).codRestrict W₀.toSubring (fun b => coe_mem Γ p j hj W₀ hW₀ b)

def centre : Ideal (OO Γ p j) := Ideal.comap (toW₀ Γ p j hj W₀ hW₀) (IsLocalRing.maximalIdeal ↥W₀)

theorem mem_centre_iff (b : OO Γ p j) : b ∈ centre Γ p j hj W₀ hW₀ ↔ (b : FG Γ) ∈ W₀.nonunits := by
  rw [centre, Ideal.mem_comap, ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
  constructor
  · intro h; exact ⟨coe_mem Γ p j hj W₀ hW₀ b, h⟩
  · rintro ⟨_, h⟩; exact h

theorem mem_centre_iff_not_isUnit (b : OO Γ p j) :
    b ∈ centre Γ p j hj W₀ hW₀ ↔ ¬ IsUnit (toW₀ Γ p j hj W₀ hW₀ b) := by
  rw [centre, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]

theorem centre_isPrime : (centre Γ p j hj W₀ hW₀).IsPrime := by
  unfold centre
  exact Ideal.comap_isPrime _ _

include hW₀ in

theorem inv_natCast_not_mem : ((p : FG Γ))⁻¹ ∉ W₀ := by
  rw [hW₀]
  rintro ⟨a, a', ha', h⟩
  apply ha'
  have hp0 : (p : FG Γ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have h3 : ((p : FG Γ) : LaurentSeries ℚ) * psQ p a = psQ p ((p : PowerSeries (Rp p)) * a) := by
    rw [psQ, psQ, map_mul, map_natCast, map_mul, map_natCast]
    push_cast
    rfl
  have h2 : psQ p a' = psQ p ((p : PowerSeries (Rp p)) * a) := by
    rw [← h3, ← h, ← mul_assoc]
    have hpp : ((p : FG Γ) : LaurentSeries ℚ) * ((((p : FG Γ))⁻¹ : FG Γ) : LaurentSeries ℚ) = 1 := by
      rw [← show (((p : FG Γ) * (p : FG Γ)⁻¹ : FG Γ) : LaurentSeries ℚ) =
          ((p : FG Γ) : LaurentSeries ℚ) * ((((p : FG Γ))⁻¹ : FG Γ) : LaurentSeries ℚ) from by push_cast; rfl,
        mul_inv_cancel₀ hp0]
      rfl
    rw [hpp, one_mul]
  rw [psQ_injective p h2, map_mul, map_natCast, ← map_natCast (PowerSeries.C (R := ZMod p)) p, ZMod.natCast_self,
    map_zero, zero_mul]

theorem natCast_mem_centre : (p : OO Γ p j) ∈ centre Γ p j hj W₀ hW₀ := by
  rw [mem_centre_iff_not_isUnit]
  intro hu
  obtain ⟨u, hu⟩ := hu
  apply inv_natCast_not_mem Γ p W₀ hW₀
  have hcoe : ((toW₀ Γ p j hj W₀ hW₀ (p : OO Γ p j) : ↥W₀) : FG Γ) = (p : FG Γ) := by
    rw [map_natCast]; norm_cast
  have h1 : ((u⁻¹ : (↥W₀)ˣ) : ↥W₀) * (u : ↥W₀) = 1 := Units.inv_mul u
  rw [hu] at h1
  have h2 := congrArg (fun z : ↥W₀ => (z : FG Γ)) h1
  have hp0 : (p : FG Γ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have : (((u⁻¹ : (↥W₀)ˣ) : ↥W₀) : FG Γ) = (p : FG Γ)⁻¹ := eq_inv_of_mul_eq_one_left h2
  rw [← this]
  exact ((u⁻¹ : (↥W₀)ˣ) : ↥W₀).2

include hj hW₀ in

theorem jInv_not_mem_centre : TwoChartIntegralModel.jInvChartInf (Rp p) (FG Γ) j ∉ centre Γ p j hj W₀ hW₀ := by
  rw [mem_centre_iff_not_isUnit, not_not]
  refine IsUnit.of_mul_eq_one ⟨(j : FG Γ), j_mem Γ p j hj W₀ hW₀⟩ (Subtype.ext ?_)
  show ((j⁻¹ : FG Γ)) * (j : FG Γ) = 1
  exact inv_mul_cancel₀ (Fact.out : j ≠ 0)

include hj in
omit hp in
theorem coeff_zero_jInv :
    (((TwoChartIntegralModel.jInvChartInf (Rp p) (FG Γ) j : FG Γ)) : LaurentSeries ℚ).coeff 0 = 0 := by
  rw [TwoChartIntegralModel.coe_jInvChartInf]
  rw [show ((j⁻¹ : FG Γ) : LaurentSeries ℚ) = ((j : FG Γ) : LaurentSeries ℚ)⁻¹ from by push_cast; rfl, hj]
  exact coeff_zero_inv_jqModC

omit hp in

theorem exists_powerSeries_of_forall_coeff_neg_eq_zero (y : LaurentSeries (Rp p))
    (hy : ∀ n : ℤ, n < 0 → y.coeff n = 0) :
    ∃ Y : PowerSeries (Rp p), HahnSeries.ofPowerSeries ℤ (Rp p) Y = y := by
  refine ⟨PowerSeries.mk fun n => y.coeff n, HahnSeries.ext (funext fun k => ?_)⟩
  rcases lt_or_ge k 0 with hk | hk
  · rw [hy k hk]
    exact ofPowerSeries_coeff_of_neg (PowerSeries.mk fun n => y.coeff n) hk
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_mk]

theorem coeffMap_ofPowerSeries {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (Y : PowerSeries A) :
    coeffMap f (HahnSeries.ofPowerSeries ℤ A Y) = HahnSeries.ofPowerSeries ℤ B (Y.map f) := by
  ext k
  rw [coeffMap_coeff]
  rcases lt_or_ge k 0 with hk | hk
  · rw [ofPowerSeries_coeff_of_neg Y hk, ofPowerSeries_coeff_of_neg (Y.map f) hk, map_zero]
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map]

include hj hW₀ in

theorem exists_psQ_eq (b : OO Γ p j) : ∃ Y : PowerSeries (Rp p), psQ p Y = ((b : FG Γ) : LaurentSeries ℚ) := by
  obtain ⟨y, hy⟩ := (exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC Γ p j hj).2 b
  have hj' : ∀ n : ℤ, n ≤ 0 → ((j : FG Γ) : LaurentSeries ℚ)⁻¹.coeff n = 0 := by
    intro n hn
    rw [hj]
    rcases hn.lt_or_eq with hlt | rfl
    · have hu : jNumQ * jNumQ.invOfUnit 1 = 1 := PowerSeries.mul_invOfUnit _ _ (by rw [constantCoeff_jNumQ]; rfl)
      have hjq : jqModC ℚ = HahnSeries.single (-1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ ℚ jNumQ := rfl
      have hinv : (jqModC ℚ)⁻¹ = HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.X * jNumQ.invOfUnit 1) := by
        apply inv_eq_of_mul_eq_one_right
        rw [hjq, map_mul, HahnSeries.ofPowerSeries_X, mul_mul_mul_comm, HahnSeries.single_mul_single, neg_add_cancel, one_mul,
          ← map_mul, hu, map_one (HahnSeries.ofPowerSeries ℤ ℚ), mul_one]
        rfl
      rw [hinv]
      exact ofPowerSeries_coeff_of_neg _ hlt
    · exact coeff_zero_inv_jqModC
  obtain ⟨ε, hε⟩ := exists_algHom_chartAlgInf_ratLocalizedAt_apply_eq_coeff_zero (qExpFunctionFieldC ℚ Γ) p j hj'
  have hneg : ∀ n : ℤ, n < 0 → y.coeff n = 0 := by
    intro n hn
    have h := (hε b).1 n hn
    rw [← hy, coeffMap_coeff] at h
    exact Subtype.coe_injective (by simpa using h)
  obtain ⟨Y, hY⟩ := exists_powerSeries_of_forall_coeff_neg_eq_zero p y hneg
  refine ⟨Y, ?_⟩
  rw [← hy, ← hY, psQ, coeffMap_ofPowerSeries]
  rfl

include hj hW₀ in

theorem isUnit_toW₀_of_isUnit_coeff (b : OO Γ p j) (Y : PowerSeries (Rp p)) (hY : psQ p Y = ((b : FG Γ) : LaurentSeries ℚ))
    (hu : IsUnit (PowerSeries.constantCoeff Y)) : IsUnit (toW₀ Γ p j hj W₀ hW₀ b) := by
  obtain ⟨u, hu⟩ := hu
  have hYinv : Y * Y.invOfUnit u = 1 := PowerSeries.mul_invOfUnit Y u hu.symm

  have hb0 : (b : FG Γ) ≠ 0 := by
    intro h0
    have : psQ p Y = 0 := by rw [hY, h0]; rfl
    have hY0 : Y = 0 := psQ_injective p (by rw [this]; simp [psQ])
    rw [hY0, map_zero] at hu
    exact u.ne_zero hu
  have hinv : ((b : FG Γ))⁻¹ ∈ W₀ := by
    rw [hW₀]
    refine ⟨Y.invOfUnit u, 1, by rw [map_one]; exact one_ne_zero, ?_⟩
    rw [show psQ p 1 = 1 from by simp [psQ], mul_one]
    have hprod : psQ p Y * psQ p (Y.invOfUnit u) = 1 := by
      rw [show psQ p Y * psQ p (Y.invOfUnit u) = psQ p (Y * Y.invOfUnit u) from by simp [psQ], hYinv]
      simp [psQ]
    rw [eq_inv_of_mul_eq_one_right hprod, hY]
    norm_cast
  refine IsUnit.of_mul_eq_one ⟨((b : FG Γ))⁻¹, hinv⟩ (Subtype.ext ?_)
  show (b : FG Γ) * (b : FG Γ)⁻¹ = 1
  exact mul_inv_cancel₀ hb0

include hj hW₀ in

theorem coeff_zero_of_mem_centre (b : OO Γ p j) (hb : b ∈ centre Γ p j hj W₀ hW₀) :
    ∃ r : ℚ, r ∈ GaloisRep.ratLocalizedAt p ∧ (((b : FG Γ)) : LaurentSeries ℚ).coeff 0 = (p : ℚ) * r := by
  obtain ⟨Y, hY⟩ := exists_psQ_eq Γ p j hj W₀ hW₀ b
  have hres : GaloisRep.ratLocalizedAtResidue p (PowerSeries.constantCoeff Y) = 0 := by
    by_contra hne
    exact (mem_centre_iff_not_isUnit Γ p j hj W₀ hW₀ b).mp hb
      (isUnit_toW₀_of_isUnit_coeff Γ p j hj W₀ hW₀ b Y hY (isUnit_of_residue_ne_zero p hne))
  obtain ⟨s, hs⟩ := exists_eq_mul_of_residue_eq_zero p hres
  refine ⟨(s : ℚ), s.2, ?_⟩
  rw [← hY, psQ, show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff, hs]
  push_cast
  rfl

def U : PowerSeries (Rp p) := PowerSeries.X * (jNum.map (Int.castRingHom (Rp p))).invOfUnit 1

theorem constantCoeff_jNum_map : PowerSeries.constantCoeff (jNum.map (Int.castRingHom (Rp p))) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff,
    constantCoeff_jNum, map_one]

theorem jNum_map_mul_invOfUnit : (jNum.map (Int.castRingHom (Rp p))) * (jNum.map (Int.castRingHom (Rp p))).invOfUnit 1 = 1 :=
  PowerSeries.mul_invOfUnit _ _ (by rw [constantCoeff_jNum_map]; rfl)

include hj in
theorem psQ_U : psQ p (U p) = ((j : FG Γ) : LaurentSeries ℚ)⁻¹ := by
  rw [hj]
  symm
  apply inv_eq_of_mul_eq_one_right
  have h1 : jqModC ℚ = HahnSeries.single (-1 : ℤ) 1 * psQ p (jNum.map (Int.castRingHom (Rp p))) := by
    rw [psQ_jNum]; rfl
  rw [h1, U, show psQ p (PowerSeries.X * (jNum.map (Int.castRingHom (Rp p))).invOfUnit 1) =
      psQ p PowerSeries.X * psQ p ((jNum.map (Int.castRingHom (Rp p))).invOfUnit 1) from by simp [psQ],
    psQ_X, mul_mul_mul_comm, HahnSeries.single_mul_single, neg_add_cancel, one_mul,
    show psQ p (jNum.map (Int.castRingHom (Rp p))) * psQ p ((jNum.map (Int.castRingHom (Rp p))).invOfUnit 1) =
      psQ p ((jNum.map (Int.castRingHom (Rp p))) * (jNum.map (Int.castRingHom (Rp p))).invOfUnit 1) from by simp [psQ],
    jNum_map_mul_invOfUnit]
  simp [psQ]

theorem coeff_U_zero : PowerSeries.coeff 0 (U p) = 0 := by
  rw [U, PowerSeries.coeff_zero_X_mul]

theorem coeff_U_one : PowerSeries.coeff 1 (U p) = 1 := by
  rw [U, show (1 : ℕ) = 0 + 1 from rfl, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have h := congrArg PowerSeries.constantCoeff (jNum_map_mul_invOfUnit p)
  rw [map_mul, constantCoeff_jNum_map, one_mul, map_one] at h
  exact h

theorem coeff_pow_of_coeff_zero_eq_zero {k : Type*} [CommRing k] (V : PowerSeries k) (hV0 : PowerSeries.coeff 0 V = 0)
    (i m : ℕ) : PowerSeries.coeff m (V ^ i) = if i ≤ m then PowerSeries.coeff (m - i) ((PowerSeries.mk fun n => PowerSeries.coeff (n + 1) V) ^ i) else 0 := by
  have hV : V = PowerSeries.X * PowerSeries.mk fun n => PowerSeries.coeff (n + 1) V := by
    have h := PowerSeries.eq_X_mul_shift_add_const V
    rw [show PowerSeries.constantCoeff V = 0 from by rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hV0], map_zero,
      add_zero] at h
    exact h
  conv_lhs => rw [hV, mul_pow]
  rw [PowerSeries.coeff_X_pow_mul']

theorem coeff_natTrailingDegree_eval₂ {k : Type*} [CommRing k] (Q : Polynomial k) (V : PowerSeries k)
    (hV0 : PowerSeries.coeff 0 V = 0) (hV1 : PowerSeries.coeff 1 V = 1) :
    PowerSeries.coeff Q.natTrailingDegree (Q.eval₂ (PowerSeries.C) V) = Q.trailingCoeff := by
  rcases eq_or_ne Q 0 with rfl | hQ
  · simp
  rw [Polynomial.eval₂_eq_sum_range, map_sum]
  rw [Finset.sum_eq_single Q.natTrailingDegree]
  · rw [PowerSeries.coeff_C_mul, coeff_pow_of_coeff_zero_eq_zero V hV0, if_pos le_rfl, Nat.sub_self,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow]
    rw [show PowerSeries.constantCoeff (PowerSeries.mk fun n => PowerSeries.coeff (n + 1) V) = 1 from by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk, zero_add, hV1], one_pow, mul_one]
    rfl
  · intro i _ hi
    rcases lt_or_gt_of_ne hi with hlt | hgt
    · rw [Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hlt, map_zero, zero_mul, map_zero]
    · rw [PowerSeries.coeff_C_mul, coeff_pow_of_coeff_zero_eq_zero V hV0, if_neg (not_le.mpr hgt), mul_zero]
  · intro h
    exfalso
    exact h (Finset.mem_range.mpr (Nat.lt_succ_of_le (Polynomial.natTrailingDegree_le_natDegree Q)))

theorem eval₂_ne_zero_of_map_ne_zero {k : Type*} [CommRing k] (Q : Polynomial k) (hQ : Q ≠ 0) (V : PowerSeries k)
    (hV0 : PowerSeries.coeff 0 V = 0) (hV1 : PowerSeries.coeff 1 V = 1) : Q.eval₂ (PowerSeries.C) V ≠ 0 := by
  intro h
  have := coeff_natTrailingDegree_eval₂ Q V hV0 hV1
  rw [h, map_zero] at this
  exact (Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr hQ) this.symm

include hj hW₀ in

theorem isUnit_toW₀_aeval (P : Polynomial (Rp p)) (hP : P.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0)
    (hmem : Polynomial.aeval (j⁻¹ : FG Γ) P ∈ TwoChartIntegralModel.chartAlgInf (Rp p) (FG Γ) j) :
    IsUnit (toW₀ Γ p j hj W₀ hW₀ ⟨Polynomial.aeval (j⁻¹ : FG Γ) P, hmem⟩) := by

  set G : PowerSeries (Rp p) := P.eval₂ PowerSeries.C (U p) with hG
  let ψ : PowerSeries (Rp p) →+* LaurentSeries ℚ :=
    (HahnSeries.ofPowerSeries ℤ ℚ).comp (PowerSeries.map (GaloisRep.ratLocalizedAt p).subtype)
  have hψ : ∀ x, psQ p x = ψ x := fun _ => rfl
  have hexp : psQ p G = ((Polynomial.aeval (j⁻¹ : FG Γ) P : FG Γ) : LaurentSeries ℚ) := by
    have h1 : ψ.comp PowerSeries.C = ((qExpFunctionFieldC ℚ Γ).toSubfield.subtype).comp (algebraMap (Rp p) (FG Γ)) := by
      refine RingHom.ext fun r => ?_
      show psQ p (PowerSeries.C r) = ((algebraMap (Rp p) (FG Γ) r : FG Γ) : LaurentSeries ℚ)
      rw [psQ, PowerSeries.map_C, HahnSeries.ofPowerSeries_C]
      rfl
    have h2 : ψ (U p) = ((qExpFunctionFieldC ℚ Γ).toSubfield.subtype) (j⁻¹ : FG Γ) := by
      rw [← hψ, psQ_U Γ p j hj]
      norm_cast
    rw [hψ, hG, Polynomial.hom_eval₂, h1, h2, ← Polynomial.hom_eval₂]
    rfl
  have hGbar : G.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 := by
    rw [hG, Polynomial.hom_eval₂, show (PowerSeries.map (GaloisRep.ratLocalizedAtResidue p)).comp PowerSeries.C =
        PowerSeries.C.comp (GaloisRep.ratLocalizedAtResidue p) from
        RingHom.ext fun r => by rw [RingHom.comp_apply, RingHom.comp_apply, PowerSeries.map_C],
      ← Polynomial.eval₂_map]
    refine eval₂_ne_zero_of_map_ne_zero _ hP _ ?_ ?_
    · rw [PowerSeries.coeff_map, coeff_U_zero, map_zero]
    · rw [PowerSeries.coeff_map, coeff_U_one, map_one]

  have hval0 : (Polynomial.aeval (j⁻¹ : FG Γ) P : FG Γ) ≠ 0 := by
    intro h0
    apply hGbar
    have : G = 0 := psQ_injective p (by rw [hexp, h0]; simp [psQ])
    rw [this, map_zero]
  have hinv : (Polynomial.aeval (j⁻¹ : FG Γ) P : FG Γ)⁻¹ ∈ W₀ := by
    rw [hW₀]
    refine ⟨1, G, hGbar, ?_⟩
    rw [show psQ p 1 = 1 from by simp [psQ], hexp]
    norm_cast
    exact inv_mul_cancel₀ hval0
  refine IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext ?_)
  show (Polynomial.aeval (j⁻¹ : FG Γ) P : FG Γ) * (Polynomial.aeval (j⁻¹ : FG Γ) P : FG Γ)⁻¹ = 1
  exact mul_inv_cancel₀ hval0

include hj hW₀ in

theorem mem_span_of_mem_adjoin_of_mem_centre (g : OO Γ p j)
    (hgA : (g : FG Γ) ∈ Algebra.adjoin (Rp p) ({j⁻¹} : Set (FG Γ))) (hg : g ∈ centre Γ p j hj W₀ hW₀) :
    g ∈ Ideal.span {(p : OO Γ p j)} := by
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hgA
  obtain ⟨P, hP⟩ := hgA

  have hPbar : P.map (GaloisRep.ratLocalizedAtResidue p) = 0 := by
    by_contra hne
    have hmem : Polynomial.aeval (j⁻¹ : FG Γ) P ∈ TwoChartIntegralModel.chartAlgInf (Rp p) (FG Γ) j := by
      rw [show Polynomial.aeval (j⁻¹ : FG Γ) P = (g : FG Γ) from hP]; exact g.2
    have hu := isUnit_toW₀_aeval Γ p j hj W₀ hW₀ P hne hmem
    have heq : (⟨Polynomial.aeval (j⁻¹ : FG Γ) P, hmem⟩ : OO Γ p j) = g := Subtype.ext hP
    rw [heq] at hu
    exact (mem_centre_iff_not_isUnit Γ p j hj W₀ hW₀ g).mp hg hu

  have hcoeff : ∀ n : ℕ, P.coeff n ∈ Ideal.span {(p : Rp p)} := fun n => by
    have h := congrArg (fun Q : Polynomial (ZMod p) => Q.coeff n) hPbar
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at h
    obtain ⟨s, hs⟩ := exists_eq_mul_of_residue_eq_zero p h
    exact Ideal.mem_span_singleton.mpr ⟨s, hs⟩
  have hPmem : P ∈ Ideal.map Polynomial.C (Ideal.span {(p : Rp p)}) := Ideal.mem_map_C_iff.mpr hcoeff
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton] at hPmem
  obtain ⟨P₂, hP₂⟩ := hPmem
  have hP₂mem : Polynomial.aeval (j⁻¹ : FG Γ) P₂ ∈ TwoChartIntegralModel.chartAlgInf (Rp p) (FG Γ) j :=
    TwoChartIntegralModel.adjoin_le_chartAlg (Rp p) (FG Γ) _
      (by rw [Algebra.adjoin_singleton_eq_range_aeval]; exact ⟨P₂, rfl⟩)
  refine Ideal.mem_span_singleton.mpr ⟨⟨_, hP₂mem⟩, Subtype.ext ?_⟩
  show (g : FG Γ) = ((p : OO Γ p j) : FG Γ) * Polynomial.aeval (j⁻¹ : FG Γ) P₂
  rw [← hP, hP₂]
  show Polynomial.aeval (j⁻¹ : FG Γ) (Polynomial.C (p : Rp p) * P₂) = _
  rw [map_mul, Polynomial.aeval_C, map_natCast]
  norm_cast

include hj hW₀ in

theorem centre_mem_minimalPrimes : centre Γ p j hj W₀ hW₀ ∈ (Ideal.span {(p : OO Γ p j)}).minimalPrimes := by
  have hAO : Aj Γ p j ≤ TwoChartIntegralModel.chartAlgInf (Rp p) (FG Γ) j :=
    TwoChartIntegralModel.adjoin_le_chartAlg (Rp p) (FG Γ) _
  letI inst : Algebra ↥(Aj Γ p j) (OO Γ p j) := (Subalgebra.inclusion hAO).toRingHom.toAlgebra
  haveI := centre_isPrime Γ p j hj W₀ hW₀
  refine ⟨⟨centre_isPrime Γ p j hj W₀ hW₀,
    (Ideal.span_singleton_le_iff_mem _).mpr (natCast_mem_centre Γ p j hj W₀ hW₀)⟩, ?_⟩
  rintro q' ⟨hq', hpq'⟩ hle
  by_contra hne
  have hlt : q' < centre Γ p j hj W₀ hW₀ := lt_of_le_of_ne hle (fun h => hne (h ▸ le_rfl))
  obtain ⟨x, hxc, hxq⟩ := SetLike.not_le_iff_exists.mp hne

  have hint : IsIntegral ↥(Aj Γ p j) x := by
    obtain ⟨P, hPm, hP0⟩ := (show IsIntegral ↥(Aj Γ p j) (x : FG Γ) from x.2)
    refine ⟨P, hPm, Subtype.ext ?_⟩
    have h := Polynomial.hom_eval₂ P (algebraMap ↥(Aj Γ p j) (OO Γ p j))
      ((TwoChartIntegralModel.chartAlgInf (Rp p) (FG Γ) j).val.toRingHom) x
    rw [show ((TwoChartIntegralModel.chartAlgInf (Rp p) (FG Γ) j).val.toRingHom).comp (algebraMap ↥(Aj Γ p j) (OO Γ p j)) =
        algebraMap ↥(Aj Γ p j) (FG Γ) from RingHom.ext fun _ => rfl] at h
    exact h.trans hP0
  haveI := hq'
  have key := Ideal.comap_lt_comap_of_integral_mem_sdiff hle ⟨hxc, hxq⟩ hint
  refine key.2 ?_
  intro g hg
  exact hpq' (mem_span_of_mem_adjoin_of_mem_centre Γ p j hj W₀ hW₀ _ g.2 hg)

end Frame

end ModularCurve.GaussCentre
p2m_reactivate "P2MW.S_ModularCurve_chartAlgInf_subset_and_exists_ideal_gaussCentre_twoChartIntegralModel_qExpFunctionFieldC.ModularCurve P2MW.S_ModularCurve_chartAlgInf_subset_and_exists_ideal_gaussCentre_twoChartIntegralModel_qExpFunctionFieldC.ModularCurve.GaussCentre"
p2m_reactivate "P2MW.S_ModularCurve_chartAlgInf_subset_and_exists_ideal_gaussCentre_twoChartIntegralModel_qExpFunctionFieldC.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_chartAlgInf_subset_and_exists_ideal_gaussCentre_twoChartIntegralModel_qExpFunctionFieldC.ModularCurve P2MW.S_ModularCurve_chartAlgInf_subset_and_exists_ideal_gaussCentre_twoChartIntegralModel_qExpFunctionFieldC.ModularCurve.GaussCentre"

open scoped MatrixGroups
p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_chartAlgInf_subset_and_exists_ideal_gaussCentre_twoChartIntegralModel_qExpFunctionFieldC.ModularCurve"

open ModularCurve.GaussCentre in
theorem solution
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ) (p : ℕ) [Fact p.Prime]
    (j : ↥(qExpFunctionFieldC ℚ Γ)) [Fact (j ≠ 0)] (hj : (j : LaurentSeries ℚ) = jqModC ℚ)
    (W₀ : ValuationSubring ↥(qExpFunctionFieldC ℚ Γ))
    (hW₀ : ∀ f : ↥(qExpFunctionFieldC ℚ Γ), f ∈ W₀ ↔
      ∃ a a' : PowerSeries ↥(GaloisRep.ratLocalizedAt p), a'.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 ∧
        (f : LaurentSeries ℚ) * HahnSeries.ofPowerSeries ℤ ℚ (a'.map (GaloisRep.ratLocalizedAt p).subtype) =
          HahnSeries.ofPowerSeries ℤ ℚ (a.map (GaloisRep.ratLocalizedAt p).subtype)) :
    (∀ b : ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j),
        (b : ↥(qExpFunctionFieldC ℚ Γ)) ∈ W₀) ∧
    ∃ 𝔮 : Ideal ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j),
      (∀ b : ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j),
        b ∈ 𝔮 ↔ (b : ↥(qExpFunctionFieldC ℚ Γ)) ∈ W₀.nonunits) ∧
      𝔮.IsPrime ∧
      ((p : ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j)) ∈ 𝔮) ∧
      𝔮 ∈ (Ideal.span {(p : ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j))}).minimalPrimes ∧
      (∀ b ∈ 𝔮, ∃ r : ℚ, r ∈ GaloisRep.ratLocalizedAt p ∧
        (((b : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ)).coeff 0 = (p : ℚ) * r) ∧
      TwoChartIntegralModel.jInvChartInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j ∉ 𝔮 ∧
      (((TwoChartIntegralModel.jInvChartInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j :
          ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ)).coeff 0 = 0 := by
  refine ⟨fun b => coe_mem Γ p j hj W₀ hW₀ b, centre Γ p j hj W₀ hW₀, mem_centre_iff Γ p j hj W₀ hW₀,
    centre_isPrime Γ p j hj W₀ hW₀, natCast_mem_centre Γ p j hj W₀ hW₀, centre_mem_minimalPrimes Γ p j hj W₀ hW₀,
    fun b hb => coeff_zero_of_mem_centre Γ p j hj W₀ hW₀ b hb, jInv_not_mem_centre Γ p j hj W₀ hW₀,
    coeff_zero_jInv Γ p j hj⟩

#print axioms solution

end S_ModularCurve_chartAlgInf_subset_and_exists_ideal_gaussCentre_twoChartIntegralModel_qExpFunctionFieldC
end P2MW
export P2MW.S_ModularCurve_chartAlgInf_subset_and_exists_ideal_gaussCentre_twoChartIntegralModel_qExpFunctionFieldC (solution)
