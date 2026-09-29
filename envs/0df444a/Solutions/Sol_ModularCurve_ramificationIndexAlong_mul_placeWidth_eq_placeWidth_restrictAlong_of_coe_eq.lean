-- Prove2me | solution 1 for ModularCurve.ramificationIndexAlong_mul_placeWidth_eq_placeWidth_restrictAlong_of_coe_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/962cbd60-5c64-5144-b8b6-b5065300df99

import Mathlib
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_PlaceWidth
import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap_eq_evalAt_restrict
import Theorems.Thm_ModularCurve_place_deg_eq_one_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_ModularCurve_coeff_jqModC_neg_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ramificationIndexAlong_mul_placeWidth_eq_placeWidth_restrictAlong_of_coe_eq
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
open AlgebraicCurve ModularCurve

namespace IdLeg

variable {k : Type*} [Field k]

theorem jGeomGen_ne_algebraMap (M : ℕ) [NeZero M] (c : k) :
    jGeomGen k M ≠ algebraMap k ↥(modularFunctionFieldC k M) c := by
  intro h
  have h1 := congrArg (fun z : ↥(modularFunctionFieldC k M) => (z : LaurentSeries k).coeff (-1 : ℤ)) h
  beta_reduce at h1
  have hl : ((jGeomGen k M : ↥(modularFunctionFieldC k M)) : LaurentSeries k).coeff (-1 : ℤ) = 1 :=
    coeff_jqModC_neg_one k
  have hr : ((algebraMap k ↥(modularFunctionFieldC k M) c : ↥(modularFunctionFieldC k M)) : LaurentSeries k).coeff (-1 : ℤ) = 0 := by
    rw [show ((algebraMap k ↥(modularFunctionFieldC k M) c : ↥(modularFunctionFieldC k M)) : LaurentSeries k)
        = algebraMap k (LaurentSeries k) c from rfl, algebraMap_laurentSeries_apply_eq_single,
      HahnSeries.coeff_single_of_ne (by decide)]
  rw [hl, hr] at h1
  exact one_ne_zero h1

end IdLeg

open IdLeg in
theorem solution
    {k : Type*} [Field k] [IsAlgClosed k] [DecidableEq k] (M M' : ℕ) [NeZero M] [NeZero M']
    (φ : ↥(modularFunctionFieldC k M) →ₐ[k] ↥(modularFunctionFieldC k M')) (hφ : φ.toRingHom.IsIntegral)
    (hcoe : ∀ x, ((φ x : ↥(modularFunctionFieldC k M')) : LaurentSeries k) = x)
    (p : Place k ↥(modularFunctionFieldC k M'))
    (hdiv : placeRamificationJ M' p ∣ jWidth (p.evalAt (jGeomGen k M'))) :
    Place.ramificationIndexAlong φ p * placeWidth M' p = placeWidth M (Place.restrictAlong φ hφ p) := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ

  set a : k := p.evalAt (jGeomGen k M') with ha
  set e : ℕ := Place.ramificationIndexAlong φ p with he_def
  have he : e = p.ramificationIndex ↥(modularFunctionFieldC k M) := rfl
  have hepos : 0 < e := he ▸ p.ramificationIndex_pos
  have hres : Place.restrictAlong φ hφ p = p.restrict ↥(modularFunctionFieldC k M) := rfl
  set x := p.restrict ↥(modularFunctionFieldC k M) with hx_def
  rw [hres]

  have hJ : φ (jGeomGen k M) = jGeomGen k M' := Subtype.ext (hcoe _)
  have hJ' : algebraMap ↥(modularFunctionFieldC k M) ↥(modularFunctionFieldC k M') (jGeomGen k M) = jGeomGen k M' := hJ

  have hWpos : 0 < jWidth a := jWidth_pos a
  have hrpos : 0 < placeRamificationJ M' p := by
    rcases Nat.eq_zero_or_pos (placeRamificationJ M' p) with h0 | h0
    · exfalso; rw [h0, zero_dvd_iff] at hdiv; exact hWpos.ne' hdiv
    · exact h0
  have hordpos : 0 < p.ord (jGeomGen k M' - algebraMap k _ a) := by
    have : 0 < (p.ord (jGeomGen k M' - algebraMap k _ a)).toNat := hrpos
    omega
  have hsub0 : jGeomGen k M' - algebraMap k _ a ≠ 0 := sub_ne_zero.mpr (jGeomGen_ne_algebraMap M' a)

  have hsub : jGeomGen k M' - algebraMap k ↥(modularFunctionFieldC k M') a
      = algebraMap ↥(modularFunctionFieldC k M) ↥(modularFunctionFieldC k M')
          (jGeomGen k M - algebraMap k ↥(modularFunctionFieldC k M) a) := by
    rw [map_sub, hJ', ← IsScalarTower.algebraMap_apply]
  have hord : p.ord (jGeomGen k M' - algebraMap k _ a)
      = e * x.ord (jGeomGen k M - algebraMap k _ a) := by
    rw [hsub, p.ord_restrict, ← he]
  have hordx : 0 < x.ord (jGeomGen k M - algebraMap k _ a) := by
    rw [hord] at hordpos
    exact pos_of_mul_pos_right hordpos (by exact_mod_cast hepos.le)

  have hxrat : x.IsRational := (Place.isRational_iff_deg_eq_one x).mpr (place_deg_eq_one_of_isAlgClosed k M x)
  have hsubx0 : jGeomGen k M - algebraMap k ↥(modularFunctionFieldC k M) a ≠ 0 :=
    sub_ne_zero.mpr (jGeomGen_ne_algebraMap M a)
  have hmemx' : jGeomGen k M - algebraMap k ↥(modularFunctionFieldC k M) a ∈ x.toValuationSubring := by

    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible x.toValuationSubring
    obtain ⟨u, hu⟩ := x.exists_unit_mul_zpow hsubx0 hπ
    rw [hu, show x.ord _ = (((x.ord (jGeomGen k M - algebraMap k _ a)).toNat : ℕ) : ℤ) from
      (Int.toNat_of_nonneg hordx.le).symm, zpow_natCast]
    exact mul_mem (u : x.toValuationSubring).2 (pow_mem (π : x.toValuationSubring).2 _)
  have hmemx : jGeomGen k M ∈ x.toValuationSubring := by
    have := add_mem hmemx' (x.algebraMap_mem' a)
    simpa using this
  have hval : x.evalAt (jGeomGen k M) = a := by
    rw [← Place.evalAt_algebraMap_eq_evalAt_restrict p hxrat hmemx, hJ']

  have hrM' : placeRamificationJ M' p = e * placeRamificationJ M x := by
    unfold placeRamificationJ
    rw [hval, hord]
    set t := x.ord (jGeomGen k M - algebraMap k ↥(modularFunctionFieldC k M) a) with ht_def
    have ht : t = ((t.toNat : ℕ) : ℤ) := (Int.toNat_of_nonneg hordx.le).symm
    conv_lhs => rw [ht, ← Nat.cast_mul, Int.toNat_natCast]
  have hrx : 0 < placeRamificationJ M x := by
    rw [hrM'] at hrpos
    exact pos_of_mul_pos_right hrpos hepos.le

  rw [hrM'] at hdiv
  obtain ⟨c, hc⟩ := hdiv
  show e * (jWidth a / placeRamificationJ M' p) = jWidth (x.evalAt (jGeomGen k M)) / placeRamificationJ M x
  rw [hval, hrM', hc, Nat.mul_div_cancel_left c (Nat.mul_pos hepos hrx),
    show e * placeRamificationJ M x * c = placeRamificationJ M x * (e * c) by ring,
    Nat.mul_div_cancel_left (e * c) hrx]

end S_ModularCurve_ramificationIndexAlong_mul_placeWidth_eq_placeWidth_restrictAlong_of_coe_eq
end P2MW
export P2MW.S_ModularCurve_ramificationIndexAlong_mul_placeWidth_eq_placeWidth_restrictAlong_of_coe_eq (solution)
