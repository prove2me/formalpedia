-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.ord_residueFst_nonneg_of_forall_reduceFst_eq_ord_nonneg_of_hasValue_atkinLehnerBar_modularUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/d2fddbab-608e-5877-a1b4-4a92d4127ef1

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_AlgebraicCurve_StandardAnnulus
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_residues_nonneg_of_forall_reduceFst_eq_ord_nonneg
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_mem_integersFst_residue_ne_zero_of_coe_eq_modularUnitSeries_level
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_residue_eq_zero_of_mem_integersSnd_of_coe_eq_modularUnitSeries
import Theorems.Thm_ModularCurve_ord_coeffEmb_modularUnitSeries_eq_zero_of_not_isCusp
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_not_isAffineGeomPlace_reduceFst_of_isCuspidal
import Theorems.Thm_ModularCurve_exists_isAtkinLehnerAutFull_of_prime_of_not_dvd
import Theorems.Thm_ModularCurve_coe_atkinLehnerInvolutionFull_modularUnitSeries
import Theorems.Thm_ModularCurve_modularUnitSeries_mem_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_atkinLehnerInvolutionFull_apply_apply
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_residueFst_nonneg_of_forall_reduceFst_eq_ord_nonneg_of_hasValue_atkinLehnerBar_modularUnit
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"
set_option Elab.async false
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open AlgebraicCurve ModularCurve ModularCurve.PlaceSpecialization
open ModularCurve.PlaceSpecialization.ProlongationTuple

namespace AtkinLehnerTransportResidue

open AlgebraicCurve ModularCurve HahnSeries IsLocalRing ModularCurve.PlaceSpecialization
open ModularCurve.PlaceSpecialization.ProlongationTuple

section PlaceHelpers
variable {K F : Type*} [Field K] [Field F] [Algebra K F] {v : Place K F}

private theorem hasValue_add {g g' : F} {a a' : K} (h : v.HasValue g a) (h' : v.HasValue g' a') :
    v.HasValue (g + g') (a + a') := by
  obtain ⟨hg, hr⟩ := h
  obtain ⟨hg', hr'⟩ := h'
  refine ⟨add_mem hg hg', ?_⟩
  have hx : (⟨g + g', add_mem hg hg'⟩ : v.toValuationSubring) = ⟨g, hg⟩ + ⟨g', hg'⟩ := rfl
  rw [hx, map_add, hr, hr', map_add]

private theorem hasValue_neg {g : F} {a : K} (h : v.HasValue g a) : v.HasValue (-g) (-a) := by
  obtain ⟨hg, hr⟩ := h
  refine ⟨neg_mem hg, ?_⟩
  have hx : (⟨-g, neg_mem hg⟩ : v.toValuationSubring) = -⟨g, hg⟩ := rfl
  rw [hx, map_neg, hr, map_neg]

private theorem hasValue_sub {g g' : F} {a a' : K} (h : v.HasValue g a) (h' : v.HasValue g' a') :
    v.HasValue (g - g') (a - a') := by
  rw [sub_eq_add_neg, sub_eq_add_neg]; exact hasValue_add h (hasValue_neg h')

private theorem ord_pos_of_hasValue_zero {g : F} (h : v.HasValue g 0) (hg : g ≠ 0) : 0 < v.ord g := by
  obtain ⟨hm, hr⟩ := h
  rw [map_zero] at hr
  exact GaussReduction.ord_pos_of_residue_eq_zero v hm hg hr

private theorem ord_nonneg_of_mem_integersPlace {g : F} (hm : g ∈ v.toValuationSubring) : 0 ≤ v.ord g := by
  by_cases hg : g = 0
  · rw [hg, Place.ord_zero]
  · exact GaussReduction.ord_nonneg_of_mem_gen v hm hg

end PlaceHelpers

private theorem inv_mem_integers_of_residue_ne_zero {L F Fbar : Type*} [Field L] [Field F] [Algebra L F] [Field Fbar]
    {A₀ : ValuationSubring L} [Algebra (IsLocalRing.ResidueField A₀) Fbar]
    (R : AlgebraicCurve.RegularProlongation A₀ F Fbar) (f : F) (h : f ∈ R.integers) (hr : R.residue ⟨f, h⟩ ≠ 0) :
    ∃ h' : f⁻¹ ∈ R.integers, R.residue ⟨f⁻¹, h'⟩ = (R.residue ⟨f, h⟩)⁻¹ := by
  obtain ⟨u, hu⟩ := R.isUnit_of_residue_ne_zero hr
  have hval : (((u⁻¹ : R.integersˣ) : R.integers) : F) = f⁻¹ := by
    have h1 : (((u⁻¹ : R.integersˣ) : R.integers) : F) * f = 1 := by
      have := congrArg (fun x : R.integers => (x : F)) u.inv_mul
      rw [hu] at this
      simpa using this
    exact eq_inv_of_mul_eq_one_left h1
  have hmem : f⁻¹ ∈ R.integers := by rw [← hval]; exact ((u⁻¹ : R.integersˣ) : R.integers).2
  refine ⟨hmem, ?_⟩
  have e : (⟨f⁻¹, hmem⟩ : R.integers) = ((u⁻¹ : R.integersˣ) : R.integers) := Subtype.ext hval.symm
  apply eq_inv_of_mul_eq_one_left
  rw [e, ← hu, ← map_mul, u.inv_mul, map_one]

private theorem _root_.ModularCurve.coeffEmb_smul' (L : Type*) [Field L] [Algebra ℚ L] (r : ℚ) (w : LaurentSeries ℚ) :
    coeffEmb L (r • w) = algebraMap L (LaurentSeries L) (algebraMap ℚ L r) * coeffEmb L w := by
  rw [algebraMap_laurentSeries_eq_single, HahnSeries.single_zero_mul_eq_smul]
  ext n
  simp only [HahnSeries.coeff_smul, coeffEmb_coeff, smul_eq_mul, map_mul]

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_residueFst_nonneg_of_forall_reduceFst_eq_ord_nonneg_of_hasValue_atkinLehnerBar_modularUnit.ModularCurve.coeffEmb_smul'" "ModularCurve.coeffEmb_smul'"

private theorem forall_ord_sub_algebraMap_le_zero_of_isCusp {K F : Type*} [Field K] [Field F] [Algebra K F]
    {j : F} {V : Place K F} (hc : IsCusp j V) (a : K) : V.ord (j - algebraMap K F a) ≤ 0 := by
  by_contra h
  push Not at h
  have hne : j - algebraMap K F a ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at h; exact lt_irrefl _ h
  have hmem : j - algebraMap K F a ∈ V.toValuationSubring := V.mem_of_ord_nonneg hne h.le
  apply hc
  have : j = (j - algebraMap K F a) + algebraMap K F a := by ring
  rw [this]
  exact add_mem hmem (V.algebraMap_mem' a)

private theorem _root_.AlgebraicCurve.Place.ord_pow' {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {g : F} (hg : g ≠ 0) (n : ℕ) : v.ord (g ^ n) = n * v.ord g := by
  induction n with
  | zero => simp [Place.ord_one]
  | succ n ih =>
    rw [pow_succ, v.ord_mul (pow_ne_zero n hg) hg, ih]
    push_cast
    ring

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_residueFst_nonneg_of_forall_reduceFst_eq_ord_nonneg_of_hasValue_atkinLehnerBar_modularUnit.AlgebraicCurve.Place.ord_pow'" "AlgebraicCurve.Place.ord_pow'"

private theorem ord_modularUnit_nonneg_of_isAffineGeomPlace_reduceFst
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (U : modularFunctionFieldBar (N * q))
    (hU : (U : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries q))
    (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (haff : IsAffineGeomPlace k N (P.reduceFst V)) : 0 ≤ V.ord U := by
  have hmem : modularUnitSeries q ∈ modularFunctionFieldFull (N * q) :=
    full_degeneracy_le (dvd_mul_left q N) (modularUnitSeries_mem_modularFunctionFieldFull q)
  have hUeq : U = ⟨coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries q),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hmem⟩ := Subtype.ext hU
  have hnc : ¬ IsCuspidal P V := fun hc => not_isAffineGeomPlace_reduceFst_of_isCuspidal P V hc haff
  have hncusp : ¬ IsCusp (CharPModel.jBar (N * q)) V := fun hc =>
    hnc (fun a => forall_ord_sub_algebraMap_le_zero_of_isCusp hc (a : AlgebraicClosure ℚ))
  rw [hUeq, ord_coeffEmb_modularUnitSeries_eq_zero_of_not_isCusp (N * q) q (dvd_mul_left q N) hmem V hncusp]

private theorem atkinLehnerBar_modularUnit
    {q : ℕ} [Fact q.Prime] (N : ℕ) [NeZero N] (hqN : ¬ q ∣ N)
    (U : modularFunctionFieldBar (N * q))
    (hU : (U : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries q)) :
    atkinLehnerBar N q U
      = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) ((q : AlgebraicClosure ℚ) ^ 12) * U⁻¹ := by
  have hmem : modularUnitSeries q ∈ modularFunctionFieldFull (N * q) :=
    full_degeneracy_le (dvd_mul_left q N) (modularUnitSeries_mem_modularFunctionFieldFull q)
  have hσ : ∃ σ : modularFunctionFieldFull (N * q) ≃ₐ[ℚ] modularFunctionFieldFull (N * q),
      IsAtkinLehnerAutFull N q σ :=
    exists_isAtkinLehnerAutFull_of_prime_of_not_dvd N q Fact.out hqN
  set u₀ : modularFunctionFieldFull (N * q) := ⟨modularUnitSeries q, hmem⟩ with hu₀
  have hUeq : U = ⟨coeffEmb (AlgebraicClosure ℚ) (u₀ : LaurentSeries ℚ),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) u₀.2⟩ := Subtype.ext hU
  apply Subtype.ext
  have hL : ((atkinLehnerBar N q U : modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ))
      = coeffEmb (AlgebraicClosure ℚ)
          ((atkinLehnerInvolutionFull N q u₀ : modularFunctionFieldFull (N * q)) : LaurentSeries ℚ) := by
    rw [hUeq]
    show ((geomAut (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q)) (atkinLehnerInvolutionFull N q)) _ :
        LaurentSeries (AlgebraicClosure ℚ)) = _
    rw [coe_geomAut_coeffEmb]
  rw [hL, hu₀, coe_atkinLehnerInvolutionFull_modularUnitSeries N q hσ hmem, coeffEmb_smul', map_inv₀, ← hU]
  have hval : ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) ((q : AlgebraicClosure ℚ) ^ 12)
        * U⁻¹ :
      modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ))
      = algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) ((q : AlgebraicClosure ℚ) ^ 12)
        * ((U : LaurentSeries (AlgebraicClosure ℚ)))⁻¹ := by
    push_cast
    rfl
  rw [hval]
  congr 2
  rw [map_pow, map_natCast]

section Tuple

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
  {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)

private theorem modularUnit_mem_integersSnd (hqN : ¬ q ∣ N) (u : modularFunctionFieldBar (N * q))
    (hu : (u : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries q))
    (hu₁ : u ∈ R.R₁.integers) (hres : R.R₁.residue ⟨u, hu₁⟩ ≠ 0) : u ∈ R.R₂.integers := by
  rw [R.mem_integersSnd_iff, ← R.mem_integersFst_iff, atkinLehnerBar_modularUnit N hqN u hu]
  obtain ⟨hinv, -⟩ := inv_mem_integers_of_residue_ne_zero R.R₁ u hu₁ hres
  exact mul_mem ((R.R₁.algebraMap_mem_iff _).mpr (pow_mem (natCast_mem A q) 12)) hinv

include R in

private theorem red_eq_zero_iff (c : A) : red c = 0 ↔ c ∈ maximalIdeal A := by
  rw [← R.redBar_residue, map_eq_zero_iff _ (R.redBar).injective, IsLocalRing.residue_eq_zero_iff]

private theorem algebraMap_mem₁ (c : A) :
    algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ) ∈ R.R₁.integers :=
  (R.R₁.algebraMap_mem_iff _).mpr c.2

private theorem algebraMap_mem₂ (c : A) :
    algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ) ∈ R.R₂.integers :=
  (R.R₂.algebraMap_mem_iff _).mpr c.2

private theorem res₂_algebraMap (c : A) :
    R.R₂.residue ⟨algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ),
        algebraMap_mem₂ R c⟩
      = algebraMap (ResidueField A) _ (IsLocalRing.residue A c) :=
  R.R₂.residue_algebraMap c

private theorem ι_algebraMap_eq_redBar (c : ResidueField A) :
    R.ι (algebraMap (ResidueField A) (modularFunctionFieldFullC (ResidueField A) N) c)
      = algebraMap k (modularFunctionFieldC k N) (R.redBar c) := by
  apply Subtype.ext
  rw [R.ι_coe]
  rw [show ((algebraMap (ResidueField A) (modularFunctionFieldFullC (ResidueField A) N) c :
      modularFunctionFieldFullC (ResidueField A) N) : LaurentSeries (ResidueField A))
      = algebraMap (ResidueField A) (LaurentSeries (ResidueField A)) c from rfl,
    show ((algebraMap k (modularFunctionFieldC k N) (R.redBar c) : modularFunctionFieldC k N) : LaurentSeries k)
      = algebraMap k (LaurentSeries k) (R.redBar c) from rfl,
    algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]

private theorem residue₂_algebraMap (c : A) :
    R.residue₂ ⟨algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ),
        algebraMap_mem₂ R c⟩
      = algebraMap k _ (red c) := by
  rw [R.residue₂_apply, res₂_algebraMap, ι_algebraMap_eq_redBar, R.redBar_residue]

private theorem res₁_algebraMap (c : A) :
    R.R₁.residue ⟨algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ),
        algebraMap_mem₁ R c⟩
      = algebraMap (ResidueField A) _ (IsLocalRing.residue A c) :=
  R.R₁.residue_algebraMap c

private theorem residue₁_algebraMap (c : A) :
    R.residue₁ ⟨algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ),
        algebraMap_mem₁ R c⟩
      = algebraMap k _ (red c) := by
  rw [R.residue₁_apply, res₁_algebraMap, ι_algebraMap_eq_redBar, R.redBar_residue]

end Tuple

section Transport

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
  {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)

private theorem atkinLehnerBar_mul_self (N q : ℕ) [NeZero N] [Fact q.Prime] (hqN : ¬ q ∣ N) :
    ProlongationTuple.atkinLehnerBar N q * ProlongationTuple.atkinLehnerBar N q = 1 := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hww : atkinLehnerInvolutionFull N q * atkinLehnerInvolutionFull N q = 1 :=
    AlgEquiv.ext fun x => by
      rw [AlgEquiv.mul_apply, AlgEquiv.one_apply]
      exact atkinLehnerInvolutionFull_apply_apply N q hqN x
  show geomAut (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q)) (atkinLehnerInvolutionFull N q) *
      geomAut (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q)) (atkinLehnerInvolutionFull N q) = 1
  rw [← map_mul, hww, map_one]

private theorem atkinLehnerBar_atkinLehnerBar (hqN : ¬ q ∣ N) (f : modularFunctionFieldBar (N * q)) :
    atkinLehnerBar N q (atkinLehnerBar N q f) = f := by
  have h := congrArg (fun e : modularFunctionFieldBar (N * q) ≃ₐ[AlgebraicClosure ℚ] modularFunctionFieldBar (N * q) =>
    e f) (atkinLehnerBar_mul_self N q hqN)
  simpa using h

private theorem mem_integersFst_atkinLehnerBar_iff (f : modularFunctionFieldBar (N * q)) :
    atkinLehnerBar N q f ∈ R.R₁.integers ↔ f ∈ R.R₂.integers := by
  rw [R.mem_integersFst_iff, R.mem_integersSnd_iff]

private theorem transport_mem₁ (u : modularFunctionFieldBar (N * q))
    (hu₂ : u ∈ R.R₂.integers) : atkinLehnerBar N q u ∈ R.R₁.integers :=
  (mem_integersFst_atkinLehnerBar_iff R u).mpr hu₂

private theorem transport_mem₂ (hqN : ¬ q ∣ N) (u : modularFunctionFieldBar (N * q))
    (hu₁ : u ∈ R.R₁.integers) : atkinLehnerBar N q u ∈ R.R₂.integers := by
  rw [← mem_integersFst_atkinLehnerBar_iff R, atkinLehnerBar_atkinLehnerBar hqN]; exact hu₁

private theorem res₁_transport_eq_zero (hqN : ¬ q ∣ N) (u : modularFunctionFieldBar (N * q))
    (hu : (u : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries q))
    (hu₁ : u ∈ R.R₁.integers) (hres : R.R₁.residue ⟨u, hu₁⟩ ≠ 0) (hu₂ : u ∈ R.R₂.integers)
    (hw₁ : atkinLehnerBar N q u ∈ R.R₁.integers) : R.R₁.residue ⟨atkinLehnerBar N q u, hw₁⟩ = 0 := by
  have h := R.residue₂_eq u hu₂
  rw [residue_eq_zero_of_mem_integersSnd_of_coe_eq_modularUnitSeries hqN P R u hu hu₁ hres hu₂] at h
  exact h.symm

private theorem ord_modularUnit_eq_zero_of_isAffineGeomPlace_reduceFst
    (U : modularFunctionFieldBar (N * q))
    (hU : (U : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries q))
    (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (haff : IsAffineGeomPlace k N (P.reduceFst V)) : V.ord U = 0 := by
  have hmem : modularUnitSeries q ∈ modularFunctionFieldFull (N * q) :=
    full_degeneracy_le (dvd_mul_left q N) (modularUnitSeries_mem_modularFunctionFieldFull q)
  have hUeq : U = ⟨coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries q),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hmem⟩ := Subtype.ext hU
  have hnc : ¬ IsCuspidal P V := fun hc => not_isAffineGeomPlace_reduceFst_of_isCuspidal P V hc haff
  have hncusp : ¬ IsCusp (CharPModel.jBar (N * q)) V := fun hc =>
    hnc (fun a => forall_ord_sub_algebraMap_le_zero_of_isCusp hc (a : AlgebraicClosure ℚ))
  rw [hUeq, ord_coeffEmb_modularUnitSeries_eq_zero_of_not_isCusp (N * q) q (dvd_mul_left q N) hmem V hncusp]

private theorem ord_transport_eq_zero_of_isAffineGeomPlace_reduceFst (hqN : ¬ q ∣ N)
    (U : modularFunctionFieldBar (N * q))
    (hU : (U : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries q))
    (hU0 : U ≠ 0)
    (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (haff : IsAffineGeomPlace k N (P.reduceFst V)) : V.ord (atkinLehnerBar N q U) = 0 := by
  have hq0 : ((q : AlgebraicClosure ℚ) ^ 12) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero)
  have hc0 : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) ((q : AlgebraicClosure ℚ) ^ 12) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).injective).mpr hq0
  rw [atkinLehnerBar_modularUnit N hqN U hU, V.ord_mul hc0 (inv_ne_zero hU0), Place.ord_inv V U,
    ord_modularUnit_eq_zero_of_isAffineGeomPlace_reduceFst (P := P) U hU V haff,
    (V.hasValue_algebraMap ((q : AlgebraicClosure ℚ) ^ 12)).ord_eq_zero hq0]
  simp

end Transport

end AtkinLehnerTransportResidue

open AtkinLehnerTransportResidue IsLocalRing HahnSeries in

theorem solution
    {N : ℕ} [NeZero N] {q : ℕ} [Fact q.Prime] (hqN : ¬ q ∣ N)
    {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k]
    [CharP k q] [IsAlgClosed k]
    [HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))]
    {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (R : ProlongationTuple P) (hR : R.IsModel) (hO : R.OrderLawFixed)
    (u : modularFunctionFieldBar (N * q))
    (hu : (u : LaurentSeries (AlgebraicClosure ℚ))
      = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries q))
    (g : modularFunctionFieldBar (N * q)) (h₁ : g ∈ R.R₁.integers) (h₂ : g ∈ R.R₂.integers)
    (hres₁ : R.R₁.residue ⟨g, h₁⟩ ≠ 0)
    (V₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hfix : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.reduceFst V₀))
      = P.reduceFst V₀)
    (haff : IsAffineGeomPlace k N (P.reduceFst V₀))
    (hpole : ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      P.reduceFst W = P.reduceFst V₀ → W ≠ V₀ → 0 ≤ W.ord g)
    (a : A) (ha : red a ≠ 0) (hV₀ : V₀.HasValue (atkinLehnerBar N q u) (a : AlgebraicClosure ℚ)) :
    0 ≤ (P.reduceFst V₀).ord (R.residue₁ ⟨g, h₁⟩) := by
  classical
  set v := P.reduceFst V₀ with hvdef

  obtain ⟨hu₁, hures₁, -⟩ := exists_mem_integersFst_residue_ne_zero_of_coe_eq_modularUnitSeries_level P R u hu
  have hu₂ : u ∈ R.R₂.integers := modularUnit_mem_integersSnd R hqN u hu hu₁ hures₁
  have hu0 : u ≠ 0 := by
    intro h0; apply hures₁
    rw [show (⟨u, hu₁⟩ : R.R₁.integers) = 0 from Subtype.ext h0, map_zero]
  set w : modularFunctionFieldBar (N * q) := atkinLehnerBar N q u with hwdef
  have hw₁ : w ∈ R.R₁.integers := transport_mem₁ R u hu₂
  have hw₂ : w ∈ R.R₂.integers := transport_mem₂ R hqN u hu₁
  have hres₁w : R.R₁.residue ⟨w, hw₁⟩ = 0 := res₁_transport_eq_zero R hqN u hu hu₁ hures₁ hu₂ hw₁

  have hV₀w : V₀.HasValue w (a : AlgebraicClosure ℚ) := hV₀

  have hg0 : g ≠ 0 := by
    intro h0; apply hres₁
    rw [show (⟨g, h₁⟩ : R.R₁.integers) = 0 from Subtype.ext h0, map_zero]

  have hca₁ := algebraMap_mem₁ R a
  set d : modularFunctionFieldBar (N * q) :=
    w - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) with hddef
  have hd₁ : d ∈ R.R₁.integers := sub_mem hw₁ hca₁
  have hd₂ : d ∈ R.R₂.integers := sub_mem hw₂ (algebraMap_mem₂ R a)
  have hresa : IsLocalRing.residue A a ≠ 0 := by
    intro h0; apply ha
    rw [red_eq_zero_iff R]; exact (IsLocalRing.residue_eq_zero_iff _).mp h0
  have hinj : Function.Injective
      (algebraMap (ResidueField A) (modularFunctionFieldFullC (ResidueField A) N)) :=
    (algebraMap (ResidueField A) (modularFunctionFieldFullC (ResidueField A) N)).injective
  have hresd₁ : R.R₁.residue ⟨d, hd₁⟩ = -algebraMap (ResidueField A) _ (IsLocalRing.residue A a) := by
    have e : (⟨d, hd₁⟩ : R.R₁.integers) = ⟨w, hw₁⟩ - ⟨_, hca₁⟩ := rfl
    rw [e, map_sub, hres₁w, res₁_algebraMap, zero_sub]
  have hresd₁ne : R.R₁.residue ⟨d, hd₁⟩ ≠ 0 := by
    rw [hresd₁, neg_ne_zero]; exact (map_ne_zero_iff _ hinj).mpr hresa
  have hd0 : d ≠ 0 := by
    intro h0; apply hresd₁ne
    rw [show (⟨d, hd₁⟩ : R.R₁.integers) = 0 from Subtype.ext h0, map_zero]

  have hdval : V₀.HasValue d 0 := by
    have := hasValue_sub hV₀w (V₀.hasValue_algebraMap (a : AlgebraicClosure ℚ))
    rwa [sub_self] at this
  have hdord : 0 < V₀.ord d := ord_pos_of_hasValue_zero hdval hd0

  have hdW : ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      P.reduceFst W = v → 0 ≤ W.ord d := by
    intro W hW
    have hwW : W.ord w = 0 :=
      ord_transport_eq_zero_of_isAffineGeomPlace_reduceFst (P := P) hqN u hu hu0 W (by rw [hW]; exact haff)
    have hw0 : w ≠ 0 := (map_ne_zero_iff _ (atkinLehnerBar N q).injective).mpr hu0
    exact ord_nonneg_of_mem_integersPlace (sub_mem (W.mem_of_ord_nonneg hw0 hwW.ge) (W.algebraMap_mem' _))

  set n : ℕ := (-(V₀.ord g)).toNat with hndef
  have hn : 0 ≤ V₀.ord g + n := by
    have := Int.self_le_toNat (-(V₀.ord g)); omega
  set H : modularFunctionFieldBar (N * q) := g * d ^ n with hHdef
  have hH₁ : H ∈ R.R₁.integers := mul_mem h₁ (pow_mem hd₁ n)
  have hH₂ : H ∈ R.R₂.integers := mul_mem h₂ (pow_mem hd₂ n)
  have hresH₁ : R.R₁.residue ⟨H, hH₁⟩ = R.R₁.residue ⟨g, h₁⟩ * R.R₁.residue ⟨d, hd₁⟩ ^ n := by
    have e : (⟨H, hH₁⟩ : R.R₁.integers) = ⟨g, h₁⟩ * ⟨d, hd₁⟩ ^ n := by
      apply Subtype.ext
      simp only [hHdef, MulMemClass.coe_mul, SubmonoidClass.coe_pow]
    rw [e, map_mul, map_pow]
  have hresH₁ne : R.R₁.residue ⟨H, hH₁⟩ ≠ 0 := by
    rw [hresH₁]; exact mul_ne_zero hres₁ (pow_ne_zero _ hresd₁ne)
  have hHreg : ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      P.reduceFst W = v → 0 ≤ W.ord H := by
    intro W hW
    rw [hHdef, W.ord_mul hg0 (pow_ne_zero _ hd0), W.ord_pow' hd0]
    by_cases hWV : W = V₀
    · subst hWV
      nlinarith [hdord, hn]
    · have h1 := hpole W hW hWV
      have h2 := hdW W hW
      positivity

  have hresH₁ne' : R.residue₁ ⟨H, hH₁⟩ ≠ 0 := by
    rw [R.residue₁_apply]; exact (map_ne_zero_iff _ R.ι.injective).mpr hresH₁ne
  have hkey : 0 ≤ v.ord (R.residue₁ ⟨H, hH₁⟩) :=
    (ord_residues_nonneg_of_forall_reduceFst_eq_ord_nonneg hqN P R hR hO H hH₁ hH₂ v hfix haff hHreg).1 hresH₁ne'

  have hres₁H : R.residue₁ ⟨H, hH₁⟩ = R.residue₁ ⟨g, h₁⟩ * (algebraMap k _ (-(red a))) ^ n := by
    rw [R.residue₁_apply, hresH₁, map_mul, map_pow, ← R.residue₁_apply, hresd₁, map_neg, map_neg,
      ← res₁_algebraMap R a, ← R.residue₁_apply, residue₁_algebraMap]
  have hc0 : (algebraMap k (modularFunctionFieldC k N) (-(red a))) ≠ 0 := by
    rw [map_ne_zero_iff _ (algebraMap k (modularFunctionFieldC k N)).injective]; exact neg_ne_zero.mpr ha
  have hg₁0 : R.residue₁ ⟨g, h₁⟩ ≠ 0 := by
    rw [R.residue₁_apply]; exact (map_ne_zero_iff _ R.ι.injective).mpr hres₁
  rw [hres₁H, v.ord_mul hg₁0 (pow_ne_zero _ hc0), v.ord_pow' hc0,
    (v.hasValue_algebraMap (-(red a))).ord_eq_zero (neg_ne_zero.mpr ha)] at hkey
  simpa using hkey

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_residueFst_nonneg_of_forall_reduceFst_eq_ord_nonneg_of_hasValue_atkinLehnerBar_modularUnit
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_residueFst_nonneg_of_forall_reduceFst_eq_ord_nonneg_of_hasValue_atkinLehnerBar_modularUnit (solution)
