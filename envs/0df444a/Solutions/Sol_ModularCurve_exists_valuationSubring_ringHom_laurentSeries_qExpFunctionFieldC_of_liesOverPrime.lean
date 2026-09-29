-- Prove2me | solution 1 for ModularCurve.exists_valuationSubring_ringHom_laurentSeries_qExpFunctionFieldC_of_liesOverPrime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/6989445d-5f00-5c65-9525-4e703179de4b

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_GaloisRep_ratLocalizedAt_maximalIdeal_eq_span_natCast
import Theorems.Thm_GaloisRep_isLocalization_ratLocalizedAt
import Theorems.Thm_ModularCurve_exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC_residue_mul_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_valuationSubring_ringHom_laurentSeries_qExpFunctionFieldC_of_liesOverPrime

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open scoped MatrixGroups
open ModularCurve IsLocalRing

namespace GaussRedH

variable (Γ : Subgroup SL(2, ℤ))

noncomputable def emb : ↥(qExpFunctionFieldC ℚ Γ) →+* ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)) :=
  ((coeffEmb (AlgebraicClosure ℚ)).comp (qExpFunctionFieldC ℚ Γ).toSubalgebra.toSubring.subtype).codRestrict
    (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))
    (fun f => coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) f.2)

@[scoped simp] theorem coe_emb (f : ↥(qExpFunctionFieldC ℚ Γ)) : ((emb Γ f : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (f : LaurentSeries ℚ) := rfl

variable {Γ}
variable {A : ValuationSubring (AlgebraicClosure ℚ)} (R : AlgebraicCurve.RegularProlongation A ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)) ↥(qExpFunctionFieldC (ResidueField ↥A) Γ))

noncomputable def V : ValuationSubring ↥(qExpFunctionFieldC ℚ Γ) := R.integers.comap (emb Γ)

theorem mem_V_iff (f : ↥(qExpFunctionFieldC ℚ Γ)) : f ∈ V R ↔ emb Γ f ∈ R.integers := Iff.rfl

noncomputable def toInt : ↥(V R) →+* ↥R.integers :=
  ((emb Γ).comp (V R).toSubring.subtype).codRestrict R.integers.toSubring (fun v => v.2)

@[scoped simp] theorem coe_toInt (v : ↥(V R)) : ((toInt R v : ↥R.integers) : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))) = emb Γ v := rfl

noncomputable def ρ : ↥(V R) →+* LaurentSeries (ResidueField ↥A) :=
  ((qExpFunctionFieldC (ResidueField ↥A) Γ).toSubalgebra.toSubring.subtype).comp (R.residue.comp (toInt R))

theorem ρ_apply (v : ↥(V R)) : ρ R v = ((R.residue (toInt R v) : ↥(qExpFunctionFieldC (ResidueField ↥A) Γ)) : LaurentSeries (ResidueField ↥A)) := rfl

theorem ρ_mem (v : ↥(V R)) : ρ R v ∈ qExpFunctionFieldC (ResidueField ↥A) Γ := (R.residue (toInt R v)).2

noncomputable def intSeries (S : Type*) [CommRing S] (p : PowerSeries ℤ) : LaurentSeries S :=
  HahnSeries.ofPowerSeries ℤ S (p.map (Int.castRingHom S))

theorem intSeries_eq_intSeriesC (K : Type*) [Field K] (p : PowerSeries ℤ) : intSeries K p = intSeriesC K p := rfl

theorem coeff_intSeries (S : Type*) [CommRing S] (p : PowerSeries ℤ) (i : ℤ) :
    (intSeries S p).coeff i = if i < 0 then 0 else ((PowerSeries.coeff i.natAbs p : ℤ) : S) := by
  unfold intSeries
  rw [show HahnSeries.ofPowerSeries ℤ S (p.map (Int.castRingHom S)) = ((p.map (Int.castRingHom S) : PowerSeries S) : LaurentSeries S)
    from rfl, PowerSeries.coeff_coe]
  split_ifs
  · rfl
  · rw [PowerSeries.coeff_map]; rfl

theorem coeffMap_intSeries {S T : Type*} [CommRing S] [CommRing T] (φ : S →+* T) (p : PowerSeries ℤ) :
    coeffMap φ (intSeries S p) = intSeries T p := by
  ext i
  rw [coeffMap_coeff, coeff_intSeries, coeff_intSeries]
  split_ifs
  · exact map_zero φ
  · exact map_intCast φ _

theorem coeffEmb_intSeriesC (p : PowerSeries ℤ) :
    coeffEmb (AlgebraicClosure ℚ) (intSeriesC ℚ p) = coeffMap A.subtype (intSeries ↥A p) := by
  rw [coeffMap_intSeries, ← intSeries_eq_intSeriesC, coeffEmb, coeffMap_intSeries]

theorem coeffMap_residue_intSeries (p : PowerSeries ℤ) :
    coeffMap (residue ↥A) (intSeries ↥A p) = intSeriesC (ResidueField ↥A) p := by
  rw [coeffMap_intSeries]; rfl

theorem intSeriesC_rat_ne_zero {p : PowerSeries ℤ} (h : intSeriesC (ResidueField ↥A) p ≠ 0) : intSeriesC ℚ p ≠ 0 := by
  intro h0
  apply h
  have hp : p = 0 := by
    ext n
    have := congrArg (fun x : LaurentSeries ℚ => x.coeff (n : ℤ)) h0
    simp only [HahnSeries.coeff_zero] at this
    rw [← intSeries_eq_intSeriesC, coeff_intSeries, if_neg (by omega), Int.natAbs_natCast, Int.cast_eq_zero] at this
    simpa using this
  rw [hp]
  exact intSeriesC_zero _

variable
  (hiii : ∀ (f : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))) (hf : f ∈ R.integers) (x y : LaurentSeries ↥A),
    coeffMap (residue ↥A) y ≠ 0 → (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x →
    ((R.residue ⟨f, hf⟩ : ↥(qExpFunctionFieldC (ResidueField ↥A) Γ)) : LaurentSeries (ResidueField ↥A)) * coeffMap (residue ↥A) y = coeffMap (residue ↥A) x)

include hiii in

theorem ρ_mul_eq (v : ↥(V R)) (y z : LaurentSeries ↥A) (hy : coeffMap (residue ↥A) y ≠ 0)
    (h : coeffEmb (AlgebraicClosure ℚ) (((v : ↥(qExpFunctionFieldC ℚ Γ))) : LaurentSeries ℚ) * coeffMap A.subtype y = coeffMap A.subtype z) :
    ρ R v * coeffMap (residue ↥A) y = coeffMap (residue ↥A) z :=
  hiii (emb Γ v) v.2 z y hy h

include hiii in

theorem ρ_eq_jqModC (j : ↥(qExpFunctionFieldC ℚ Γ)) (hj : (j : LaurentSeries ℚ) = jqModC ℚ) (v : ↥(V R)) (hv : (v : ↥(qExpFunctionFieldC ℚ Γ)) = j) :
    ρ R v = jqModC (ResidueField ↥A) := by
  have h1 : coeffMap (residue ↥A) (1 : LaurentSeries ↥A) ≠ 0 := by rw [map_one]; exact one_ne_zero
  have h := ρ_mul_eq R hiii v 1 (jqModC ↥A) h1 (by
    rw [map_one, mul_one, hv, hj]
    show coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (jqModC ℚ) = coeffMap A.subtype (jqModC ↥A)
    change (jqModC ℚ).map (algebraMap ℚ (AlgebraicClosure ℚ)) = (jqModC ↥A).map A.subtype
    rw [map_jqModC, map_jqModC])
  rw [map_one, mul_one] at h
  rw [h]
  change (jqModC ↥A).map (residue ↥A) = _
  exact map_jqModC _

variable
  (hi : ∀ f : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)), f ∈ R.integers ↔
    ∃ x y : LaurentSeries ↥A, coeffMap (residue ↥A) y ≠ 0 ∧ (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)

include hi hiii in

theorem adjoin_range_ρ : IntermediateField.adjoin (ResidueField ↥A) (Set.range (ρ R)) = qExpFunctionFieldC (ResidueField ↥A) Γ := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨v, rfl⟩
    exact ρ_mem R v
  · change IntermediateField.adjoin (ResidueField ↥A) (intFormRatiosC (ResidueField ↥A) Γ) ≤ _
    apply IntermediateField.adjoin.mono
    rintro _ ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩

    have hg0ℚ : intSeriesC ℚ pg ≠ 0 := intSeriesC_rat_ne_zero hg0
    let u : ↥(qExpFunctionFieldC ℚ Γ) := ⟨intSeriesC ℚ pf / intSeriesC ℚ pg, div_mem_qExpFunctionFieldC f g hf hg hg0ℚ⟩
    have hybar : coeffMap (residue ↥A) (intSeries ↥A pg) ≠ 0 := by rwa [coeffMap_residue_intSeries]
    have hinjι : Function.Injective (coeffMap A.subtype) := by
      intro a b hab
      ext i
      have := congrArg (fun x : LaurentSeries (AlgebraicClosure ℚ) => x.coeff i) hab
      simp only [coeffMap_coeff] at this
      exact this
    have hy0 : coeffMap A.subtype (intSeries ↥A pg) ≠ 0 := fun h0 =>
      hybar (by rw [(injective_iff_map_eq_zero _).1 hinjι _ h0, map_zero])
    have heq : coeffEmb (AlgebraicClosure ℚ) ((u : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ) * coeffMap A.subtype (intSeries ↥A pg) =
        coeffMap A.subtype (intSeries ↥A pf) := by
      change coeffEmb (AlgebraicClosure ℚ) (intSeriesC ℚ pf / intSeriesC ℚ pg) * _ = _
      rw [map_div₀, coeffEmb_intSeriesC, coeffEmb_intSeriesC, div_mul_cancel₀ _ hy0]
    have hu : u ∈ V R := (mem_V_iff R u).2 ((hi _).2 ⟨intSeries ↥A pf, intSeries ↥A pg, hybar, heq⟩)
    refine ⟨⟨u, hu⟩, ?_⟩
    have h := ρ_mul_eq R hiii ⟨u, hu⟩ (intSeries ↥A pg) (intSeries ↥A pf) hybar heq
    rw [coeffMap_residue_intSeries, coeffMap_residue_intSeries] at h
    rw [eq_div_iff hg0]
    exact h

section aevalNat
variable {S T : Type*} [CommRing S] [CommRing T]

theorem algebraMap_laurentSeries_eq_single' (a : S) : algebraMap S (LaurentSeries S) a = HahnSeries.single 0 a := by
  show HahnSeries.ofPowerSeries ℤ S (PowerSeries.C a) = _
  exact HahnSeries.ofPowerSeries_C a

theorem coeffMap_algebraMap' (φ : S →+* T) (a : S) :
    coeffMap φ (algebraMap S (LaurentSeries S) a) = algebraMap T (LaurentSeries T) (φ a) := by
  rw [algebraMap_laurentSeries_eq_single', algebraMap_laurentSeries_eq_single', coeffMap_single]

theorem coeffMap_eval₂ (φ : S →+* T) (x : LaurentSeries S) (P : Polynomial S) :
    coeffMap φ (Polynomial.eval₂ (algebraMap S (LaurentSeries S)) x P) =
      Polynomial.eval₂ (algebraMap T (LaurentSeries T)) (coeffMap φ x) (P.map φ) := by
  rw [Polynomial.hom_eval₂, Polynomial.eval₂_map]
  congr 1
  ext a : 1
  exact coeffMap_algebraMap' φ a

end aevalNat

variable (p : ℕ) [Fact p.Prime]

theorem coeffEmb_aeval_eq_coeffMap_aeval (j : ↥(qExpFunctionFieldC ℚ Γ)) (hj : (j : LaurentSeries ℚ) = jqModC ℚ)
    (ρ₀ : ↥(GaloisRep.ratLocalizedAt p) →+* ↥A) (hρ₀ : A.subtype.comp ρ₀ = algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))
    (halg : ∀ r : ↥(GaloisRep.ratLocalizedAt p), ((algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) r : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ) = algebraMap ℚ (LaurentSeries ℚ) (r : ℚ))
    (P : Polynomial ↥(GaloisRep.ratLocalizedAt p)) :
    coeffEmb (AlgebraicClosure ℚ) ((Polynomial.aeval j P : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ) =
      coeffMap A.subtype (Polynomial.aeval (jqModC ↥A) (P.map ρ₀)) := by

  have h1 : ((Polynomial.aeval j P : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ) =
      Polynomial.eval₂ (algebraMap ℚ (LaurentSeries ℚ)) (jqModC ℚ) (P.map (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ)) := by
    rw [Polynomial.aeval_def, ← hj, Polynomial.eval₂_map]
    change (qExpFunctionFieldC ℚ Γ).toSubalgebra.toSubring.subtype (Polynomial.eval₂ _ j P) = _
    rw [Polynomial.hom_eval₂]
    congr 1
    ext r : 1
    exact halg r
  rw [h1, Polynomial.aeval_def, coeffEmb, coeffMap_eval₂, coeffMap_eval₂, Polynomial.map_map, Polynomial.map_map]
  congr 1
  · change (jqModC ℚ).map _ = (jqModC ↥A).map _
    rw [map_jqModC, map_jqModC]
  · congr 1
    ext r : 1
    change algebraMap ℚ (AlgebraicClosure ℚ) (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ r) = A.subtype (ρ₀ r)
    rw [← IsScalarTower.algebraMap_apply ↥(GaloisRep.ratLocalizedAt p) ℚ (AlgebraicClosure ℚ), ← hρ₀]
    rfl

theorem coeffMap_residue_aeval (ρ₀ : ↥(GaloisRep.ratLocalizedAt p) →+* ↥A) (P : Polynomial ↥(GaloisRep.ratLocalizedAt p)) :
    coeffMap (residue ↥A) (Polynomial.aeval (jqModC ↥A) (P.map ρ₀)) =
      Polynomial.aeval (jqModC (ResidueField ↥A)) (P.map ((residue ↥A).comp ρ₀)) := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def, coeffMap_eval₂, Polynomial.map_map]
  congr 1
  change (jqModC ↥A).map _ = _
  exact map_jqModC _

include hi in

theorem mem_V_iff_gauss (f : ↥(qExpFunctionFieldC ℚ Γ)) :
    f ∈ V R ↔ ∃ y z : LaurentSeries ↥A, coeffMap (residue ↥A) y ≠ 0 ∧
      coeffEmb (AlgebraicClosure ℚ) ((f : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ) * coeffMap A.subtype y =
        coeffMap A.subtype z := by
  rw [mem_V_iff, hi, ← coe_emb]
  constructor
  · rintro ⟨x, y, hy, h⟩; exact ⟨y, x, hy, h⟩
  · rintro ⟨y, z, hy, h⟩; exact ⟨z, y, hy, h⟩

theorem ρ_eq_zero_of_mem_nonunits (v : ↥(V R)) (hv : (v : ↥(qExpFunctionFieldC ℚ Γ)) ∈ (V R).nonunits) : ρ R v = 0 := by

  have hvmax : v ∈ IsLocalRing.maximalIdeal ↥(V R) := ValuationSubring.coe_mem_nonunits_iff.mp hv
  have hnu : toInt R v ∈ IsLocalRing.maximalIdeal ↥R.integers := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hvmax
    apply hvmax

    obtain ⟨u, hu⟩ := hu
    have hv0 : (v : ↥(qExpFunctionFieldC ℚ Γ)) ≠ 0 := by
      intro h0
      have : (toInt R v : ↥R.integers) = 0 := by
        apply Subtype.ext
        rw [coe_toInt, h0, map_zero]; rfl
      rw [← hu] at this
      exact u.ne_zero this
    have hinv : (v : ↥(qExpFunctionFieldC ℚ Γ))⁻¹ ∈ V R := by
      rw [mem_V_iff, map_inv₀]
      have : ((emb Γ v : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))))⁻¹ =
          ((u⁻¹ : (↥R.integers)ˣ) : ↥R.integers) := by
        rw [← coe_toInt, ← hu]
        symm
        apply eq_inv_of_mul_eq_one_left
        have h1 := congrArg (fun w : ↥R.integers => (w : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)))) u.inv_mul
        exact h1
      rw [this]
      exact ((u⁻¹ : (↥R.integers)ˣ) : ↥R.integers).2
    refine ⟨⟨v, ⟨(v : ↥(qExpFunctionFieldC ℚ Γ))⁻¹, hinv⟩, ?_, ?_⟩, rfl⟩
    · apply Subtype.ext; exact mul_inv_cancel₀ hv0
    · apply Subtype.ext; exact inv_mul_cancel₀ hv0
  rw [← R.ker_residue, RingHom.mem_ker] at hnu
  rw [ρ_apply, hnu]
  rfl

theorem ratLocalizedAt_isUnit_of_not_dvd (p : ℕ) [Fact p.Prime] (c : ↥(GaloisRep.ratLocalizedAt p))
    (hc : ¬ ((p : ↥(GaloisRep.ratLocalizedAt p)) ∣ c)) : IsUnit c := by
  have hp : p.Prime := Fact.out
  haveI : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr (Nat.prime_iff_prime_int.mp hp)
  haveI := GaloisRep.isLocalization_ratLocalizedAt hp
  haveI : IsLocalRing ↥(GaloisRep.ratLocalizedAt p) :=
    IsLocalization.AtPrime.isLocalRing ↥(GaloisRep.ratLocalizedAt p) (Ideal.span {(p : ℤ)})
  by_contra h
  have hmem : c ∈ IsLocalRing.maximalIdeal ↥(GaloisRep.ratLocalizedAt p) := h
  rw [GaloisRep.ratLocalizedAt.maximalIdeal_eq_span_natCast p hp, Ideal.mem_span_singleton] at hmem
  exact hc hmem

theorem coeffMap_subtype_injective : Function.Injective (coeffMap A.subtype) := by
  intro a b hab
  ext i
  have := congrArg (fun x : LaurentSeries (AlgebraicClosure ℚ) => x.coeff i) hab
  simp only [coeffMap_coeff] at this
  exact this

include hi in

theorem aeval_mem_V_and_inv_mem_V (p : ℕ) [Fact p.Prime] (j : ↥(qExpFunctionFieldC ℚ Γ))
    (ρ₀ : ↥(GaloisRep.ratLocalizedAt p) →+* ↥A)
    (hnat : ∀ P : Polynomial ↥(GaloisRep.ratLocalizedAt p),
      coeffEmb (AlgebraicClosure ℚ) ((Polynomial.aeval j P : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ) =
        coeffMap A.subtype (Polynomial.aeval (jqModC ↥A) (P.map ρ₀)))
    (hred : ∀ P : Polynomial ↥(GaloisRep.ratLocalizedAt p),
      coeffMap (residue ↥A) (Polynomial.aeval (jqModC ↥A) (P.map ρ₀)) =
        Polynomial.aeval (jqModC (ResidueField ↥A)) (P.map ((residue ↥A).comp ρ₀)))
    (P : Polynomial ↥(GaloisRep.ratLocalizedAt p)) (hP : ¬ (Polynomial.C (p : ↥(GaloisRep.ratLocalizedAt p)) ∣ P)) :
    Polynomial.aeval j P ∈ V R ∧ (Polynomial.aeval j P)⁻¹ ∈ V R := by
  set y := Polynomial.aeval (jqModC ↥A) (P.map ρ₀) with hy

  have hPbar : P.map ((residue ↥A).comp ρ₀) ≠ 0 := by
    rw [Polynomial.C_dvd_iff_dvd_coeff] at hP
    push Not at hP
    obtain ⟨i, hi'⟩ := hP
    intro h0
    have hc := congrArg (fun Q => Polynomial.coeff Q i) h0
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero, RingHom.coe_comp, Function.comp_apply] at hc
    rw [IsLocalRing.residue_eq_zero_iff] at hc
    exact (IsLocalRing.mem_maximalIdeal _).mp hc ((ratLocalizedAt_isUnit_of_not_dvd p _ hi').map ρ₀)
  have hybar : coeffMap (residue ↥A) y ≠ 0 := by
    rw [hy, hred]
    intro h0
    exact hPbar (transcendental_iff.mp (transcendental_jqModC (ResidueField ↥A)) _ h0)
  have hy0 : coeffMap A.subtype y ≠ 0 := fun h0 =>
    hybar (by rw [(injective_iff_map_eq_zero _).1 coeffMap_subtype_injective _ h0, map_zero])
  have hemb : ((emb Γ (Polynomial.aeval j P) : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))) :
      LaurentSeries (AlgebraicClosure ℚ)) = coeffMap A.subtype y := by
    rw [coe_emb, hnat]
  refine ⟨(mem_V_iff R _).mpr ((hi _).mpr ⟨y, 1, by rw [map_one]; exact one_ne_zero, ?_⟩),
    (mem_V_iff R _).mpr ((hi _).mpr ⟨1, y, hybar, ?_⟩)⟩
  · rw [hemb, map_one, mul_one]
  · rw [map_inv₀, map_one]
    push_cast
    rw [hemb, inv_mul_cancel₀ hy0]

section constants

variable (p : ℕ) [Fact p.Prime]
  (ρ₀ : ↥(GaloisRep.ratLocalizedAt p) →+* ↥A)
  (hρ₀ : A.subtype.comp ρ₀ = algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))

theorem coeffEmb_algebraMap_rat (r : ℚ) :
    coeffEmb (AlgebraicClosure ℚ) (algebraMap ℚ (LaurentSeries ℚ) r) =
      algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (algebraMap ℚ (AlgebraicClosure ℚ) r) := by
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffEmb, coeffMap_single]

include hρ₀ in
theorem coe_ρ₀ (r : ↥(GaloisRep.ratLocalizedAt p)) : ((ρ₀ r : ↥A) : AlgebraicClosure ℚ) = algebraMap ℚ (AlgebraicClosure ℚ) (r : ℚ) := by
  have h := congrArg (fun φ => φ r) hρ₀
  simp only [RingHom.comp_apply] at h
  rw [show ((ρ₀ r : ↥A) : AlgebraicClosure ℚ) = A.subtype (ρ₀ r) from rfl, h,
    IsScalarTower.algebraMap_apply ↥(GaloisRep.ratLocalizedAt p) ℚ (AlgebraicClosure ℚ)]
  rfl

theorem coe_algebraMap_F (q : ℚ) :
    ((algebraMap ℚ ↥(qExpFunctionFieldC ℚ Γ) q : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ) = algebraMap ℚ (LaurentSeries ℚ) q := by
  rw [eq_ratCast, SubfieldClass.coe_ratCast, ← eq_ratCast (algebraMap ℚ (LaurentSeries ℚ)) q]

theorem coe_algebraMap_LF (c : AlgebraicClosure ℚ) :
    ((algebraMap (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)) c :
      ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))) : LaurentSeries (AlgebraicClosure ℚ)) =
      algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) c := rfl

theorem algebraMap_ratLocalizedAt_apply (r : ↥(GaloisRep.ratLocalizedAt p)) :
    algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ r = (r : ℚ) := rfl

include hρ₀ in

theorem emb_algebraMap (r : ↥(GaloisRep.ratLocalizedAt p)) :
    emb Γ (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) r) =
      algebraMap (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)) ((ρ₀ r : ↥A) : AlgebraicClosure ℚ) := by
  apply Subtype.ext
  rw [coe_emb, coe_ρ₀ p ρ₀ hρ₀, IsScalarTower.algebraMap_apply ↥(GaloisRep.ratLocalizedAt p) ℚ ↥(qExpFunctionFieldC ℚ Γ),
    coe_algebraMap_F, coe_algebraMap_LF, algebraMap_ratLocalizedAt_apply]
  exact coeffEmb_algebraMap_rat _

theorem coe_algebraMap_ratLocalizedAt (r : ↥(GaloisRep.ratLocalizedAt p)) :
    ((algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) r : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ) =
      algebraMap ℚ (LaurentSeries ℚ) (r : ℚ) := by
  rw [IsScalarTower.algebraMap_apply ↥(GaloisRep.ratLocalizedAt p) ℚ ↥(qExpFunctionFieldC ℚ Γ), coe_algebraMap_F,
    algebraMap_ratLocalizedAt_apply]

include hρ₀ in

theorem algebraMap_mem_V (r : ↥(GaloisRep.ratLocalizedAt p)) :
    algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) r ∈ V R := by
  rw [mem_V_iff, emb_algebraMap p ρ₀ hρ₀, R.algebraMap_mem_iff]
  exact (ρ₀ r).2

include hρ₀ in

theorem natCast_mem_nonunits (hA : A.LiesOverPrime p) :
    algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) (p : ↥(GaloisRep.ratLocalizedAt p)) ∈ (V R).nonunits := by
  set x := algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) (p : ↥(GaloisRep.ratLocalizedAt p)) with hxdef
  have hx : x ∈ V R := algebraMap_mem_V R p ρ₀ hρ₀ _
  refine (ValuationSubring.coe_mem_nonunits_iff (a := ⟨x, hx⟩)).mpr ((IsLocalRing.mem_maximalIdeal _).mpr fun hu => ?_)

  obtain ⟨u, hu⟩ := hu
  have hpL : ((ρ₀ (p : ↥(GaloisRep.ratLocalizedAt p)) : ↥A) : AlgebraicClosure ℚ) = (p : AlgebraicClosure ℚ) := by
    rw [coe_ρ₀ p ρ₀ hρ₀]; simp
  have hp0 : (p : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hmul : ((u : ↥(V R)) : ↥(qExpFunctionFieldC ℚ Γ)) * (((u⁻¹ : (↥(V R))ˣ) : ↥(V R)) : ↥(qExpFunctionFieldC ℚ Γ)) = 1 := by
    rw [← MulMemClass.coe_mul, Units.mul_inv, OneMemClass.coe_one]
  have hinvV : x⁻¹ ∈ V R := by
    have : x⁻¹ = (((u⁻¹ : (↥(V R))ˣ) : ↥(V R)) : ↥(qExpFunctionFieldC ℚ Γ)) := by
      rw [show x = ((u : ↥(V R)) : ↥(qExpFunctionFieldC ℚ Γ)) from congrArg Subtype.val hu.symm]
      exact inv_eq_of_mul_eq_one_right hmul
    rw [this]; exact SetLike.coe_mem _
  have hinvA : ((p : AlgebraicClosure ℚ))⁻¹ ∈ A := by
    have h1 : emb Γ x⁻¹ ∈ R.integers := hinvV
    rw [map_inv₀, emb_algebraMap p ρ₀ hρ₀, ← map_inv₀, R.algebraMap_mem_iff, hpL] at h1
    exact h1

  have hpm : (⟨(p : AlgebraicClosure ℚ), A.nonunits_subset hA⟩ : ↥A) ∈ maximalIdeal ↥A :=
    (ValuationSubring.coe_mem_nonunits_iff).mp hA
  refine (IsLocalRing.mem_maximalIdeal _).mp hpm (IsUnit.of_mul_eq_one (b := ⟨_, hinvA⟩) (Subtype.ext ?_))
  change (p : AlgebraicClosure ℚ) * ((p : AlgebraicClosure ℚ))⁻¹ = 1
  exact mul_inv_cancel₀ hp0

include hρ₀ in

theorem ρ_algebraMap (r : ↥(GaloisRep.ratLocalizedAt p)) :
    letI := ((residue ↥A).comp ρ₀).toAlgebra
    ρ R ⟨algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) r, algebraMap_mem_V R p ρ₀ hρ₀ r⟩ =
      algebraMap (ResidueField ↥A) (LaurentSeries (ResidueField ↥A))
        (algebraMap ↥(GaloisRep.ratLocalizedAt p) (ResidueField ↥A) r) := by
  letI := ((residue ↥A).comp ρ₀).toAlgebra
  rw [ρ_apply]
  have h1 : toInt R ⟨algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) r, algebraMap_mem_V R p ρ₀ hρ₀ r⟩ =
      ⟨algebraMap (AlgebraicClosure ℚ) _ ((ρ₀ r : ↥A) : AlgebraicClosure ℚ), (R.algebraMap_mem_iff _).mpr (ρ₀ r).2⟩ :=
    Subtype.ext (emb_algebraMap p ρ₀ hρ₀ r)
  rw [h1, R.residue_algebraMap]
  rfl

end constants

end GaussRedH
p2m_reactivate "P2MW.S_ModularCurve_exists_valuationSubring_ringHom_laurentSeries_qExpFunctionFieldC_of_liesOverPrime.GaussRedH"

open GaussRedH in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in

theorem solution
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ) (p : ℕ) [Fact p.Prime]
    (j : ↥(qExpFunctionFieldC ℚ Γ)) (hj : (j : LaurentSeries ℚ) = jqModC ℚ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (ρ₀ : ↥(GaloisRep.ratLocalizedAt p) →+* ↥A)
    (hρ₀ : A.subtype.comp ρ₀ = algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))
    (x : ↥(qExpFunctionFieldC (ResidueField ↥A) Γ))
    (hx : (x : LaurentSeries (ResidueField ↥A)) = jqModC (ResidueField ↥A)) :
    letI := ((residue ↥A).comp ρ₀).toAlgebra
    ∃ (V : ValuationSubring ↥(qExpFunctionFieldC ℚ Γ))
      (hRV : ∀ r : ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) r ∈ V)
      (ρ : ↥V →+* LaurentSeries (ResidueField ↥A)),
      algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) (p : ↥(GaloisRep.ratLocalizedAt p)) ∈ V.nonunits ∧
      (∀ P : Polynomial ↥(GaloisRep.ratLocalizedAt p), ¬ (Polynomial.C (p : ↥(GaloisRep.ratLocalizedAt p)) ∣ P) →
        Polynomial.aeval j P ∈ V ∧ (Polynomial.aeval j P)⁻¹ ∈ V) ∧
      (∀ v : ↥V, (v : ↥(qExpFunctionFieldC ℚ Γ)) ∈ V.nonunits → ρ v = 0) ∧
      (∀ r : ↥(GaloisRep.ratLocalizedAt p),
        ρ ⟨algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) r, hRV r⟩ =
          algebraMap (ResidueField ↥A) (LaurentSeries (ResidueField ↥A))
            (algebraMap ↥(GaloisRep.ratLocalizedAt p) (ResidueField ↥A) r)) ∧
      (∀ v : ↥V, (v : ↥(qExpFunctionFieldC ℚ Γ)) = j → ρ v = jqModC (ResidueField ↥A)) ∧
      IntermediateField.adjoin (ResidueField ↥A) (Set.range ρ) = qExpFunctionFieldC (ResidueField ↥A) Γ ∧
      (∀ f : ↥(qExpFunctionFieldC ℚ Γ), f ∈ V ↔
        ∃ y z : LaurentSeries ↥A, coeffMap (residue ↥A) y ≠ 0 ∧
          coeffEmb (AlgebraicClosure ℚ) ((f : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ) * coeffMap A.subtype y =
            coeffMap A.subtype z) ∧
      (∀ (v : ↥V) (y z : LaurentSeries ↥A), coeffMap (residue ↥A) y ≠ 0 →
          coeffEmb (AlgebraicClosure ℚ) (((v : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ)) * coeffMap A.subtype y =
            coeffMap A.subtype z →
        ρ v * coeffMap (residue ↥A) y = coeffMap (residue ↥A) z) := by
  letI instAlg := ((residue ↥A).comp ρ₀).toAlgebra
  obtain ⟨R, hi, hii, hiii⟩ :=
    ModularCurve.exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC_residue_mul_eq (AlgebraicClosure ℚ) A Γ hT
  refine ⟨V R, algebraMap_mem_V R p ρ₀ hρ₀, ρ R, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact natCast_mem_nonunits R p ρ₀ hρ₀ hA
  · exact fun P hP => aeval_mem_V_and_inv_mem_V R hi p j ρ₀
      (coeffEmb_aeval_eq_coeffMap_aeval p j hj ρ₀ hρ₀ (coe_algebraMap_ratLocalizedAt p)) (coeffMap_residue_aeval p ρ₀) P hP
  · exact fun v hv => ρ_eq_zero_of_mem_nonunits R v hv
  · exact fun r => ρ_algebraMap R p ρ₀ hρ₀ r
  · exact fun v hv => ρ_eq_jqModC R hiii j hj v hv
  · exact adjoin_range_ρ R hiii hi
  · exact fun f => mem_V_iff_gauss R hi f
  · exact fun v y z hy h => ρ_mul_eq R hiii v y z hy h

end S_ModularCurve_exists_valuationSubring_ringHom_laurentSeries_qExpFunctionFieldC_of_liesOverPrime
end P2MW
export P2MW.S_ModularCurve_exists_valuationSubring_ringHom_laurentSeries_qExpFunctionFieldC_of_liesOverPrime (solution)
