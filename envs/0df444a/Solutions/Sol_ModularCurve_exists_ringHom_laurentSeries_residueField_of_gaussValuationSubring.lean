-- Prove2me | solution 1 for ModularCurve.exists_ringHom_laurentSeries_residueField_of_gaussValuationSubring
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/cfa46765-110e-514e-9776-b6e49b14e150

import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_ringHom_laurentSeries_residueField_of_gaussValuationSubring

set_option autoImplicit false

open IsLocalRing ModularCurve

namespace IgusaNodesE133

section Gauss

variable {L : Type*} [Field L] (A : ValuationSubring L)

noncomputable abbrev emb : LaurentSeries ↥A →+* LaurentSeries L := coeffMap A.subtype

noncomputable abbrev red : LaurentSeries ↥A →+* LaurentSeries (ResidueField ↥A) :=
  coeffMap (IsLocalRing.residue ↥A)

theorem emb_injective : Function.Injective (emb A) := by
  intro x y h
  ext k
  have := congrArg (fun z : LaurentSeries L => z.coeff k) h
  simp only [emb, coeffMap_coeff] at this
  exact congrArg Subtype.val (A.subtype_injective this)

variable {A}

theorem cross_eq {f : LaurentSeries L} {x y x' y' : LaurentSeries ↥A}
    (h : f * emb A y = emb A x) (h' : f * emb A y' = emb A x') : x * y' = x' * y := by
  apply emb_injective A
  rw [map_mul, map_mul, ← h, ← h']
  ring

theorem red_cross_eq {f : LaurentSeries L} {x y x' y' : LaurentSeries ↥A}
    (h : f * emb A y = emb A x) (h' : f * emb A y' = emb A x') :
    red A x * red A y' = red A x' * red A y := by
  rw [← map_mul, ← map_mul, cross_eq h h']

variable (A)
variable {F : IntermediateField L (LaurentSeries L)} (O : ValuationSubring ↥F)
  (hO : ∀ f : ↥F, f ∈ O ↔ ∃ x y : LaurentSeries ↥A, red A y ≠ 0 ∧
    (f : LaurentSeries L) * emb A y = emb A x)

noncomputable def gaussRes (f : ↥O) : LaurentSeries (ResidueField ↥A) :=
  red A ((hO (f : ↥F)).mp f.2).choose / red A ((hO (f : ↥F)).mp f.2).choose_spec.choose

variable {A O hO}

theorem gaussRes_mul_eq_of_pres (f : ↥O) {x' y' : LaurentSeries ↥A} (hy' : red A y' ≠ 0)
    (h' : ((f : ↥F) : LaurentSeries L) * emb A y' = emb A x') :
    gaussRes A O hO f * red A y' = red A x' := by
  obtain ⟨hy, h⟩ := ((hO (f : ↥F)).mp f.2).choose_spec.choose_spec
  unfold gaussRes
  rw [div_mul_eq_mul_div, red_cross_eq h h', mul_div_assoc, div_self hy, mul_one]

theorem gaussRes_eq_div_of_pres (f : ↥O) {x' y' : LaurentSeries ↥A} (hy' : red A y' ≠ 0)
    (h' : ((f : ↥F) : LaurentSeries L) * emb A y' = emb A x') :
    gaussRes A O hO f = red A x' / red A y' :=
  eq_div_of_mul_eq hy' (gaussRes_mul_eq_of_pres f hy' h')

variable (A O hO)

noncomputable def gaussResHom : ↥O →+* LaurentSeries (ResidueField ↥A) where
  toFun := gaussRes A O hO
  map_one' := by
    rw [gaussRes_eq_div_of_pres (1 : ↥O) (x' := 1) (y' := 1) (by simp) (by simp), map_one, div_one]
  map_mul' f g := by
    obtain ⟨x, y, hy, h⟩ := (hO (f : ↥F)).mp f.2
    obtain ⟨x', y', hy', h'⟩ := (hO (g : ↥F)).mp g.2
    have hfg : (((f * g : ↥O) : ↥F) : LaurentSeries L) * emb A (y * y') = emb A (x * x') := by
      push_cast
      rw [map_mul, map_mul, ← h, ← h']
      ring
    rw [gaussRes_eq_div_of_pres (f * g) (by rw [map_mul]; exact mul_ne_zero hy hy') hfg,
      gaussRes_eq_div_of_pres f hy h, gaussRes_eq_div_of_pres g hy' h', map_mul, map_mul,
      div_mul_div_comm]
  map_zero' := by
    rw [gaussRes_eq_div_of_pres (0 : ↥O) (x' := 0) (y' := 1) (by simp) (by simp), map_zero, zero_div]
  map_add' f g := by
    obtain ⟨x, y, hy, h⟩ := (hO (f : ↥F)).mp f.2
    obtain ⟨x', y', hy', h'⟩ := (hO (g : ↥F)).mp g.2
    have hfg : (((f + g : ↥O) : ↥F) : LaurentSeries L) * emb A (y * y') = emb A (x * y' + x' * y) := by
      push_cast
      rw [map_mul, map_add, map_mul, map_mul, ← h, ← h']
      ring
    rw [gaussRes_eq_div_of_pres (f + g) (by rw [map_mul]; exact mul_ne_zero hy hy') hfg,
      gaussRes_eq_div_of_pres f hy h, gaussRes_eq_div_of_pres g hy' h', map_add, map_mul, map_mul,
      map_mul, div_add_div _ _ hy hy']
    ring

variable {A O hO}

theorem gaussResHom_apply (f : ↥O) : gaussResHom A O hO f = gaussRes A O hO f := rfl

theorem gaussResHom_mul_eq_of_pres (f : ↥O) {x' y' : LaurentSeries ↥A} (hy' : red A y' ≠ 0)
    (h' : ((f : ↥F) : LaurentSeries L) * emb A y' = emb A x') :
    gaussResHom A O hO f * red A y' = red A x' := by
  rw [gaussResHom_apply]; exact gaussRes_mul_eq_of_pres f hy' h'

theorem gaussResHom_eq_div_of_pres (f : ↥O) {x' y' : LaurentSeries ↥A} (hy' : red A y' ≠ 0)
    (h' : ((f : ↥F) : LaurentSeries L) * emb A y' = emb A x') :
    gaussResHom A O hO f = red A x' / red A y' := by
  rw [gaussResHom_apply]; exact gaussRes_eq_div_of_pres f hy' h'

theorem isUnit_of_gaussResHom_ne_zero (f : ↥O) (hf : gaussResHom A O hO f ≠ 0) : IsUnit f := by
  obtain ⟨x, y, hy, h⟩ := (hO (f : ↥F)).mp f.2
  have hx : red A x ≠ 0 := by
    intro hx
    apply hf
    rw [gaussResHom_eq_div_of_pres f hy h, hx, zero_div]
  have hf0 : ((f : ↥F) : LaurentSeries L) ≠ 0 := by
    intro h0
    apply hx
    rw [h0, zero_mul] at h
    rw [emb_injective A (h.symm.trans (map_zero (emb A)).symm), map_zero]
  have hf0' : (f : ↥F) ≠ 0 := fun h0 => hf0 (by rw [h0]; rfl)
  have hinv : ((f : ↥F)⁻¹ : ↥F) ∈ O := by
    refine (hO _).mpr ⟨y, x, hx, ?_⟩
    have : (((f : ↥F)⁻¹ : ↥F) : LaurentSeries L) = ((f : ↥F) : LaurentSeries L)⁻¹ := by
      push_cast; rfl
    rw [this, ← h, ← mul_assoc, inv_mul_cancel₀ hf0, one_mul]
  exact isUnit_iff_exists_inv.mpr ⟨⟨(f : ↥F)⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hf0')⟩

theorem gaussResHom_eq_zero_iff (f : ↥O) : gaussResHom A O hO f = 0 ↔ ¬ IsUnit f := by
  constructor
  · intro h0 hu
    obtain ⟨g, hg⟩ := hu.exists_right_inv
    have := congrArg (gaussResHom A O hO) hg
    rw [map_mul, h0, zero_mul, map_one] at this
    exact zero_ne_one this
  · intro hnu
    by_contra h0
    exact hnu (isUnit_of_gaussResHom_ne_zero f h0)

theorem ker_gaussResHom : RingHom.ker (gaussResHom A O hO) = maximalIdeal ↥O := by
  ext f
  rw [RingHom.mem_ker, gaussResHom_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]

end Gauss

section Theta

variable {L : Type*} [Field L] (A : ValuationSubring L)
  {F : IntermediateField L (LaurentSeries L)} {Fbar : Type*} [Field Fbar] [Algebra (ResidueField ↥A) Fbar]
  (R : AlgebraicCurve.RegularProlongation A ↥F Fbar)
  (hO : ∀ f : ↥F, f ∈ R.integers ↔ ∃ x y : LaurentSeries ↥A, red A y ≠ 0 ∧
    (f : LaurentSeries L) * emb A y = emb A x)

theorem exists_theta :
    ∃ θ : Fbar →+* LaurentSeries (ResidueField ↥A),
      ∀ f : ↥R.integers, θ (R.residue f) = gaussResHom A R.integers hO f := by
  let Ψ := gaussResHom A R.integers hO
  have hle : RingHom.ker R.residue ≤ RingHom.ker Ψ := by
    rw [R.ker_residue, ker_gaussResHom]
  let e : (↥R.integers ⧸ RingHom.ker R.residue) ≃+* Fbar :=
    RingHom.quotientKerEquivOfSurjective R.residue_surjective
  let ψ : (↥R.integers ⧸ RingHom.ker R.residue) →+* LaurentSeries (ResidueField ↥A) :=
    Ideal.Quotient.lift (RingHom.ker R.residue) Ψ (fun a ha => (RingHom.mem_ker).mp (hle ha))
  refine ⟨ψ.comp e.symm.toRingHom, fun f => ?_⟩
  have he : e.symm (R.residue f) = Ideal.Quotient.mk (RingHom.ker R.residue) f := by
    apply e.injective
    rw [RingEquiv.apply_symm_apply]
    exact (RingHom.quotientKerEquivOfSurjective_apply_mk R.residue_surjective f).symm
  rw [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, he, Ideal.Quotient.lift_mk]

end Theta

end IgusaNodesE133

theorem solution
    {L : Type*} [Field L] (A : ValuationSubring L) (F : IntermediateField L (LaurentSeries L))
    (W : ValuationSubring ↥F)
    (hW : ∀ f : ↥F, f ∈ W ↔ ∃ x y : LaurentSeries ↥A, coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
      (f : LaurentSeries L) * coeffMap A.subtype y = coeffMap A.subtype x) :
    ∃ red : ↥W →+* LaurentSeries (IsLocalRing.ResidueField ↥A),
      (∀ f : ↥W, red f = 0 ↔ (f : ↥F) ∈ W.nonunits) ∧
      ∀ (f : ↥W) (x y : LaurentSeries ↥A), coeffMap (IsLocalRing.residue ↥A) y ≠ 0 →
        ((f : ↥F) : LaurentSeries L) * coeffMap A.subtype y = coeffMap A.subtype x →
        red f * coeffMap (IsLocalRing.residue ↥A) y = coeffMap (IsLocalRing.residue ↥A) x := by
  refine ⟨IgusaNodesE133.gaussResHom A W hW, fun f => ?_, fun f x y hy h => ?_⟩
  · rw [IgusaNodesE133.gaussResHom_eq_zero_iff, ValuationSubring.coe_mem_nonunits_iff,
      IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  · exact IgusaNodesE133.gaussResHom_mul_eq_of_pres f hy h

end S_ModularCurve_exists_ringHom_laurentSeries_residueField_of_gaussValuationSubring
end P2MW
export P2MW.S_ModularCurve_exists_ringHom_laurentSeries_residueField_of_gaussValuationSubring (solution)
