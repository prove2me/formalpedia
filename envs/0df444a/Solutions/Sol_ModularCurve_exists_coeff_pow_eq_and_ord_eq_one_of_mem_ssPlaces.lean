-- Prove2me | solution 1 for ModularCurve.exists_coeff_pow_eq_and_ord_eq_one_of_mem_ssPlaces
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/f96920a9-8e2b-537a-98a9-80994642cc75

import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_AlgebraicCurve_ConstantFieldPullback
import Theorems.Thm_AlgebraicCurve_Place_ramificationIndex_forgetConstants_eq_one_of_isConstantFieldExtension
import Theorems.Thm_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension_of_isAlgClosed
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldC_of_perfectField
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_isSeparable_jqNModC_of_natCast_ne_zero
import Theorems.Thm_ModularCurve_finiteDimensional_and_isSeparable_adjoin_jGeomGen_of_isSeparable_jqNModC
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_LaurentSeries_eq_C_coeff_zero_of_isAlgebraic
import Theorems.Thm_ModularCurve_pow_q_sq_eq_self_of_mem_ssJSet
import Theorems.Thm_ValuationSubring_isPrincipalIdealRing_of_finiteDimensional_adjoin
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_coeff_pow_eq_and_ord_eq_one_of_mem_ssPlaces
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆"
p2m_attr_erase "simp" "Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

noncomputable section

p2m_open "AlgebraicCurve IsLocalRing ModularCurve~transcendental_jq"
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple
open scoped IntermediateField.algebraAdjoinAdjoin

namespace SupersingularUniformiser

section Transport

variable {K K' : Type*} [Field K] [Field K'] (σ : K →+* K') (N : ℕ) [NeZero N]

private theorem coeffMap_mem_FC {x : LaurentSeries K} (hx : x ∈ modularFunctionFieldC K N) :
    coeffMap σ x ∈ modularFunctionFieldC K' N := by
  change x ∈ Subfield.closure (Set.range (algebraMap K (LaurentSeries K)) ∪
      {jqModC K, jqNModC K N}) at hx
  induction hx using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨a, rfl⟩ | hy
      · have h1 : coeffMap σ (algebraMap K (LaurentSeries K) a)
            = algebraMap K' (LaurentSeries K') (σ a) := by
          rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]
        rw [h1]
        exact (modularFunctionFieldC K' N).algebraMap_mem _
      · rcases hy with rfl | hy
        · rw [coeffSemilinearAut.coeffMap_jqModC]
          exact jqModC_mem K' N
        · rw [Set.mem_singleton_iff] at hy
          subst hy
          rw [coeffSemilinearAut.coeffMap_jqNModC]
          exact jqNModC_mem K' N
  | one => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | neg x _ hx => simpa using neg_mem hx
  | inv x _ hx => simpa using inv_mem hx
  | mul x y _ _ hx hy => simpa using mul_mem hx hy

private def fcMap : ↥(modularFunctionFieldC K N) →+* ↥(modularFunctionFieldC K' N) where
  toFun x := ⟨coeffMap σ (x : LaurentSeries K), coeffMap_mem_FC σ N x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

private theorem fcMap_coe (x : ↥(modularFunctionFieldC K N)) :
    ((fcMap σ N x : ↥(modularFunctionFieldC K' N)) : LaurentSeries K') = coeffMap σ (x : LaurentSeries K) :=
  rfl

private theorem fcMap_algebraMap (a : K) :
    fcMap σ N (algebraMap K ↥(modularFunctionFieldC K N) a)
      = algebraMap K' ↥(modularFunctionFieldC K' N) (σ a) := by
  apply Subtype.ext
  rw [fcMap_coe]
  change coeffMap σ (algebraMap K (LaurentSeries K) a) = algebraMap K' (LaurentSeries K') (σ a)
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]

private theorem fcMap_jq :
    fcMap σ N (⟨jqModC K, jqModC_mem K N⟩ : ↥(modularFunctionFieldC K N))
      = ⟨jqModC K', jqModC_mem K' N⟩ :=
  Subtype.ext (coeffSemilinearAut.coeffMap_jqModC σ)

private theorem fcMap_jqN :
    fcMap σ N (⟨jqNModC K N, jqNModC_mem K N⟩ : ↥(modularFunctionFieldC K N))
      = ⟨jqNModC K' N, jqNModC_mem K' N⟩ :=
  Subtype.ext (coeffSemilinearAut.coeffMap_jqNModC σ N)

end Transport

section Packages

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]

private theorem transcendental_jq : Transcendental K (⟨jqModC K, jqModC_mem K N⟩ : ↥(modularFunctionFieldC K N)) :=
  fun h => transcendental_jqModC K (h.algebraMap (A := LaurentSeries K))

private theorem finite_and_separable (hN : (N : K) ≠ 0) :
    FiniteDimensional (IntermediateField.adjoin K
        ({(⟨jqModC K, jqModC_mem K N⟩ : ↥(modularFunctionFieldC K N))} : Set ↥(modularFunctionFieldC K N)))
      ↥(modularFunctionFieldC K N) ∧
    Algebra.IsSeparable (IntermediateField.adjoin K
        ({(⟨jqModC K, jqModC_mem K N⟩ : ↥(modularFunctionFieldC K N))} : Set ↥(modularFunctionFieldC K N)))
      ↥(modularFunctionFieldC K N) := by
  have hsep := isSeparable_jqNModC_of_natCast_ne_zero K N hN
  obtain ⟨data⟩ := nonempty_modularPolynomialData N
  exact finiteDimensional_and_isSeparable_adjoin_jGeomGen_of_isSeparable_jqNModC K N data hsep

private theorem hfg_package (hN : (N : K) ≠ 0) :
    ∃ x : ↥(modularFunctionFieldC K N), Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set ↥(modularFunctionFieldC K N)))
        ↥(modularFunctionFieldC K N) :=
  ⟨_, transcendental_jq K N, (finite_and_separable K N hN).1⟩

end Packages

section LB

private theorem div_cancel_aux {F : Type*} [Field F] {A B p : F} (hB : B ≠ 0) (hp : p ≠ 0) {m n : ℕ} (hmn : n ≤ m) :
    A * B⁻¹ * p ^ (m - n) = A * p ^ m / (B * p ^ n) := by
  rw [eq_div_iff (mul_ne_zero hB (pow_ne_zero n hp))]
  calc A * B⁻¹ * p ^ (m - n) * (B * p ^ n) = A * (B⁻¹ * B) * (p ^ (m - n) * p ^ n) := by ring
    _ = A * p ^ m := by rw [inv_mul_cancel₀ hB, mul_one, ← pow_add, Nat.sub_add_cancel hmn]

private theorem mul_div_cancel_aux {F : Type*} [Field F] {A B p : F} (hA : A ≠ 0) (hB : B ≠ 0) (hp : p ≠ 0) {m n : ℕ}
    (hmn : m ≤ n) : B * A⁻¹ * p ^ (n - m) * (A * p ^ m / (B * p ^ n)) = 1 := by
  rw [div_eq_mul_inv]
  calc B * A⁻¹ * p ^ (n - m) * (A * p ^ m * (B * p ^ n)⁻¹)
      = (A⁻¹ * A) * ((B * (p ^ (n - m) * p ^ m)) * (B * p ^ n)⁻¹) := by ring
    _ = 1 := by
      rw [inv_mul_cancel₀ hA, one_mul, ← pow_add, Nat.sub_add_cancel hmn,
        mul_inv_cancel₀ (mul_ne_zero hB (pow_ne_zero n hp))]

private theorem eq_zero_of_map_eq_zero {C F : Type*} [CommRing C] [Field F] [Algebra C F] [IsFractionRing C F]
    (V : ValuationSubring F) (ι : C →+* ↥V) (hι : ∀ c, ((ι c : ↥V) : F) = algebraMap C F c)
    {c : C} (hc : ι c = 0) : c = 0 := by
  apply IsFractionRing.injective C F
  rw [map_zero, ← hι c, hc]
  rfl

private theorem inv_mem_of_isUnit {C F : Type*} [CommRing C] [Field F] [Algebra C F]
    (V : ValuationSubring F) (ι : C →+* ↥V) (hι : ∀ c, ((ι c : ↥V) : F) = algebraMap C F c)
    {c : C} (hc : IsUnit (ι c)) : (algebraMap C F c)⁻¹ ∈ V := by
  obtain ⟨w, hw⟩ := hc.exists_right_inv
  by_cases hc0 : algebraMap C F c = 0
  · rw [hc0, inv_zero]; exact zero_mem _
  · have hw' : algebraMap C F c * (w : F) = 1 := by
      have := congrArg (fun z : ↥V => (z : F)) hw
      simpa [hι] using this
    rw [(eq_inv_of_mul_eq_one_left hw' : algebraMap C F c = ((w : F))⁻¹), inv_inv]
    exact w.2

private theorem isUnit_map_primeCompl {C F : Type*} [CommRing C] [Field F] (V : ValuationSubring F) (ι : C →+* ↥V)
    (y : (Ideal.comap ι (maximalIdeal ↥V)).primeCompl) : IsUnit (ι y) := by
  obtain ⟨y, hy⟩ := y
  by_contra hu
  apply hy
  change ι y ∈ maximalIdeal ↥V
  rw [mem_maximalIdeal, mem_nonunits_iff]; exact hu

private theorem isField_of_comap_eq_bot {C F : Type*} [CommRing C] [IsDomain C] [Field F] [Algebra C F]
    [IsFractionRing C F] (V : ValuationSubring F) (ι : C →+* ↥V)
    (hι : ∀ c, ((ι c : ↥V) : F) = algebraMap C F c)
    (hP : Ideal.comap ι (maximalIdeal ↥V) = ⊥) : IsField ↥V := by
  have hunit : ∀ c : C, c ≠ 0 → IsUnit (ι c) := by
    intro c hc
    by_contra hu
    have : c ∈ Ideal.comap ι (maximalIdeal ↥V) := by
      change ι c ∈ maximalIdeal ↥V
      rw [mem_maximalIdeal, mem_nonunits_iff]; exact hu
    rw [hP, Ideal.mem_bot] at this
    exact hc this
  refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, fun {v} hv => ?_⟩
  obtain ⟨c, d, hd, hcd⟩ := IsFractionRing.div_surjective (A := C) (v : F)
  have hv0 : (v : F) ≠ 0 := fun h => hv (Subtype.ext h)
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hv0
    rw [← hcd, map_zero, zero_div]
  have hmem : ((v : F))⁻¹ ∈ V := by
    rw [← hcd, inv_div, div_eq_mul_inv]
    refine mul_mem ?_ (inv_mem_of_isUnit V ι hι (hunit c hc0))
    rw [← hι d]; exact (ι d).2
  exact ⟨⟨((v : F))⁻¹, hmem⟩, Subtype.ext (mul_inv_cancel₀ hv0)⟩

private theorem exists_irreducible_map_of_comap_ne_bot {C F : Type*} [CommRing C] [IsDomain C] [Field F]
    [Algebra C F] [IsFractionRing C F] (V : ValuationSubring F) (hV : V ≠ ⊤) (ι : C →+* ↥V)
    (hι : ∀ c, ((ι c : ↥V) : F) = algebraMap C F c)
    [IsDedekindDomain C] (hP : Ideal.comap ι (maximalIdeal ↥V) ≠ ⊥) :
    ∃ c : C, Irreducible (ι c) := by
  classical
  set P : Ideal C := Ideal.comap ι (maximalIdeal ↥V) with hPdef
  haveI hPprime : P.IsPrime := Ideal.comap_isPrime ι (maximalIdeal ↥V)
  haveI hDVR : IsDiscreteValuationRing (Localization.AtPrime P) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain C hP (Localization.AtPrime P)
  haveI hDpid : IsPrincipalIdealRing (Localization.AtPrime P) :=
    @IsDiscreteValuationRing.toIsPrincipalIdealRing _ _ _ hDVR
  have hunits : ∀ y : P.primeCompl, IsUnit (ι y) := isUnit_map_primeCompl V ι
  let ψ : Localization.AtPrime P →+* ↥V := IsLocalization.lift hunits
  have hψalg : ∀ c, ψ (algebraMap C (Localization.AtPrime P) c) = ι c := fun c => IsLocalization.lift_eq hunits c
  have hinjC : Function.Injective (algebraMap C (Localization.AtPrime P)) :=
    IsLocalization.injective (Localization.AtPrime P) P.primeCompl_le_nonZeroDivisors

  have hψinj : ∀ z, ψ z = 0 → z = 0 := by
    intro z hz
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl z
    rw [IsLocalization.lift_mk'] at hz
    have ha : ι a = 0 := (Units.mul_left_eq_zero _).mp hz
    have ha0 : a = 0 := eq_zero_of_map_eq_zero V ι hι ha
    change IsLocalization.mk' (Localization.AtPrime P) a s = 0
    rw [ha0, IsLocalization.mk'_zero]
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime P)

  have hψϖ : ¬ IsUnit (ψ ϖ) := by
    intro hu
    apply hP
    refine (Submodule.eq_bot_iff P).mpr fun c hc => ?_
    by_contra hc0
    have hcD : algebraMap C (Localization.AtPrime P) c ≠ 0 := fun h => hc0 (hinjC (by rw [h, map_zero]))
    obtain ⟨n, u, hcu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hcD hϖ
    have : IsUnit (ι c) := by
      rw [← hψalg c, hcu, map_mul, map_pow]
      exact (u.isUnit.map ψ).mul (hu.pow n)
    have hc' : ι c ∈ maximalIdeal ↥V := hc
    rw [mem_maximalIdeal, mem_nonunits_iff] at hc'
    exact hc' this

  have hψinv : ∀ u : (Localization.AtPrime P)ˣ,
      ((ψ ((u⁻¹ : (Localization.AtPrime P)ˣ) : Localization.AtPrime P) : ↥V) : F)
        = (((ψ (u : Localization.AtPrime P) : ↥V) : F))⁻¹ := by
    intro u
    apply eq_inv_of_mul_eq_one_left
    have : ψ ((u⁻¹ : (Localization.AtPrime P)ˣ) : Localization.AtPrime P) * ψ (u : Localization.AtPrime P) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    have := congrArg (fun t : ↥V => (t : F)) this
    simpa using this
  have hψu0 : ∀ u : (Localization.AtPrime P)ˣ, ((ψ (u : Localization.AtPrime P) : ↥V) : F) ≠ 0 := fun u h =>
    (u.isUnit.map ψ).ne_zero (Subtype.ext h)

  have hsurj : Function.Surjective ψ := by
    intro v
    by_cases hv0 : (v : F) = 0
    · exact ⟨0, Subtype.ext (by rw [map_zero]; exact hv0.symm)⟩
    obtain ⟨c, d, hd, hcd⟩ := IsFractionRing.div_surjective (A := C) (v : F)
    have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
    have hc0 : c ≠ 0 := by
      rintro rfl
      apply hv0
      rw [← hcd, map_zero, zero_div]
    have hcD : algebraMap C (Localization.AtPrime P) c ≠ 0 := fun h => hc0 (hinjC (by rw [h, map_zero]))
    have hdD : algebraMap C (Localization.AtPrime P) d ≠ 0 := fun h => hd0 (hinjC (by rw [h, map_zero]))
    obtain ⟨m, u₁, hcu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hcD hϖ
    obtain ⟨n, u₂, hdu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hdD hϖ
    have hcF : algebraMap C F c = ((ψ (u₁ : Localization.AtPrime P) : ↥V) : F) * ((ψ ϖ : ↥V) : F) ^ m := by
      rw [← hι c, ← hψalg c, hcu, map_mul, map_pow]
      rfl
    have hdF : algebraMap C F d = ((ψ (u₂ : Localization.AtPrime P) : ↥V) : F) * ((ψ ϖ : ↥V) : F) ^ n := by
      rw [← hι d, ← hψalg d, hdu, map_mul, map_pow]
      rfl
    have hϖ0 : ((ψ ϖ : ↥V) : F) ≠ 0 := fun h => hϖ.ne_zero (hψinj ϖ (Subtype.ext h))
    by_cases hmn : n ≤ m
    · refine ⟨(u₁ : Localization.AtPrime P) * (u₂⁻¹ : (Localization.AtPrime P)ˣ) * ϖ ^ (m - n), ?_⟩
      apply Subtype.ext
      rw [map_mul, map_mul, map_pow]
      change ((ψ (u₁ : Localization.AtPrime P) : ↥V) : F) *
          ((ψ ((u₂⁻¹ : (Localization.AtPrime P)ˣ) : Localization.AtPrime P) : ↥V) : F) *
          ((ψ ϖ : ↥V) : F) ^ (m - n) = (v : F)
      rw [hψinv u₂, ← hcd, hcF, hdF]
      exact div_cancel_aux (hψu0 u₂) hϖ0 hmn
    · exfalso
      have hmn' : m < n := not_le.mp hmn
      have hk' : 0 < n - m := Nat.sub_pos_of_lt hmn'
      have hwv : ψ ((u₂ : Localization.AtPrime P) * (u₁⁻¹ : (Localization.AtPrime P)ˣ) * ϖ ^ (n - m)) * v
          = 1 := by
        apply Subtype.ext
        rw [map_mul, map_mul, map_pow]
        change ((ψ (u₂ : Localization.AtPrime P) : ↥V) : F) *
            ((ψ ((u₁⁻¹ : (Localization.AtPrime P)ˣ) : Localization.AtPrime P) : ↥V) : F) *
            ((ψ ϖ : ↥V) : F) ^ (n - m) * (v : F) = 1
        rw [hψinv u₁, ← hcd, hcF, hdF]
        exact mul_div_cancel_aux (hψu0 u₁) (hψu0 u₂) hϖ0 hmn'.le
      have hwunit := IsUnit.of_mul_eq_one _ hwv
      rw [map_mul, map_mul, map_pow] at hwunit
      exact hψϖ ((isUnit_pow_iff hk'.ne').mp (IsUnit.mul_iff.mp hwunit).2)

  haveI hVpir : IsPrincipalIdealRing ↥V := IsPrincipalIdealRing.of_surjective ψ hsurj
  haveI hVdvr : IsDiscreteValuationRing ↥V :=
    { not_a_field' := fun h =>
        ValuationSubring.not_isField_of_ne_top F hV ((IsLocalRing.isField_iff_maximalIdeal_eq).mpr h) }
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible ↥V
  obtain ⟨z, hz⟩ := hsurj π
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact hπ.ne_zero (by rw [← hz, map_zero])
  obtain ⟨m, u, hzu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hz0 hϖ
  have hψϖirr : Irreducible (ψ ϖ) := by
    cases m with
    | zero =>
      exfalso
      apply hπ.1
      rw [← hz, hzu, pow_zero, mul_one]
      exact u.isUnit.map ψ
    | succ m' =>
      have hfac : π = ψ ϖ * (ψ (u : Localization.AtPrime P) * ψ ϖ ^ m') := by
        rw [← hz, hzu, map_mul, map_pow, pow_succ]
        ring
      rcases hπ.2 hfac with hu1 | hu2
      · exact absurd hu1 hψϖ
      · have : Irreducible (ψ ϖ * (ψ (u : Localization.AtPrime P) * ψ ϖ ^ m')) := by rw [← hfac]; exact hπ
        exact (irreducible_mul_isUnit hu2).mp this

  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl ϖ
  refine ⟨a, ?_⟩
  have h := hψϖirr
  rw [IsLocalization.lift_mk'] at h
  exact (irreducible_mul_isUnit (Units.isUnit _)).mp h

private theorem mem_of_isIntegral_adjoin {k F : Type*} [Field k] [Field F] [Algebra k F] (x : F)
    (V' : ValuationSubring F) (hk : ∀ a : k, algebraMap k F a ∈ V') (hxV : x ∈ V')
    {c : F} (hc : IsIntegral ↥(Algebra.adjoin k ({x} : Set F)) c) : c ∈ V' := by
  have hRV : ∀ y ∈ Algebra.adjoin k ({x} : Set F), y ∈ V' := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem z hz =>
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact hxV
    | algebraMap r => exact hk r
    | add _ _ _ _ h1 h2 => exact add_mem h1 h2
    | mul _ _ _ _ h1 h2 => exact mul_mem h1 h2
  let φRV : ↥(Algebra.adjoin k ({x} : Set F)) →+* ↥V' :=
    { toFun := fun y => ⟨y.1, hRV y.1 y.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  obtain ⟨p, hmon, hp⟩ := hc
  have hcV : IsIntegral ↥V' c := ⟨p.map φRV, hmon.map _, by rw [Polynomial.eval₂_map]; exact hp⟩
  obtain ⟨y, hy⟩ := (IsIntegrallyClosedIn.isIntegral_iff (R := ↥V') (A := F)).mp hcV
  rw [← hy]
  exact y.2

private theorem exists_ord_eq_one_of_transcendental
    {k F : Type*} [Field k] [Field F] [Algebra k F] (x : F) (hx : Transcendental k x)
    [FiniteDimensional ↥(IntermediateField.adjoin k ({x} : Set F)) F]
    [Algebra.IsSeparable ↥(IntermediateField.adjoin k ({x} : Set F)) F]
    (v : Place k F) (hxv : x ∈ v.toValuationSubring) :
    ∃ t : F, (∀ V' : ValuationSubring F, (∀ a : k, algebraMap k F a ∈ V') → x ∈ V' → t ∈ V') ∧
      v.ord t = 1 := by
  classical
  haveI hRpid : IsPrincipalIdealRing ↥(Algebra.adjoin k ({x} : Set F)) :=
    IsPrincipalIdealRing.of_surjective (Polynomial.algEquivOfTranscendental k x hx).toRingHom
      (Polynomial.algEquivOfTranscendental k x hx).surjective
  haveI hRded : IsDedekindDomain ↥(Algebra.adjoin k ({x} : Set F)) := inferInstance
  haveI hCded : IsDedekindDomain ↥(integralClosure ↥(Algebra.adjoin k ({x} : Set F)) F) :=
    integralClosure.isDedekindDomain ↥(Algebra.adjoin k ({x} : Set F))
      ↥(IntermediateField.adjoin k ({x} : Set F)) F
  haveI hCfrac : IsFractionRing ↥(integralClosure ↥(Algebra.adjoin k ({x} : Set F)) F) F :=
    IsIntegralClosure.isFractionRing_of_finite_extension ↥(Algebra.adjoin k ({x} : Set F))
      ↥(IntermediateField.adjoin k ({x} : Set F)) F ↥(integralClosure ↥(Algebra.adjoin k ({x} : Set F)) F)
  let ι : ↥(integralClosure ↥(Algebra.adjoin k ({x} : Set F)) F) →+* ↥v.toValuationSubring :=
    { toFun := fun c => ⟨c.1, mem_of_isIntegral_adjoin x v.toValuationSubring v.algebraMap_mem' hxv
        ((mem_integralClosure_iff _ _).mp c.2)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hP : Ideal.comap ι (maximalIdeal ↥v.toValuationSubring) ≠ ⊥ := fun hP =>
    ValuationSubring.not_isField_of_ne_top F v.ne_top' (isField_of_comap_eq_bot _ ι (fun _ => rfl) hP)
  obtain ⟨c, hc⟩ := exists_irreducible_map_of_comap_ne_bot _ v.ne_top' ι (fun _ => rfl) hP
  refine ⟨(c : F), fun V' hk hxV' => mem_of_isIntegral_adjoin x V' hk hxV' ((mem_integralClosure_iff _ _).mp c.2),
    ?_⟩
  exact v.ord_coe_irreducible hc

end LB

section Induction

variable {K : Type*} [Field K] (N : ℕ) [NeZero N]

private theorem FC_induction (P : ↥(modularFunctionFieldC K N) → Prop)
    (hconst : ∀ a : K, P (algebraMap K ↥(modularFunctionFieldC K N) a))
    (hj : P ⟨jqModC K, jqModC_mem K N⟩) (hjN : P ⟨jqNModC K N, jqNModC_mem K N⟩)
    (hadd : ∀ x y, P x → P y → P (x + y)) (hinv : ∀ x, P x → P x⁻¹)
    (hmul : ∀ x y, P x → P y → P (x * y)) (x : ↥(modularFunctionFieldC K N)) : P x := by
  obtain ⟨x, hx⟩ := x
  change x ∈ IntermediateField.adjoin K ({jqModC K, jqNModC K N} : Set (LaurentSeries K)) at hx
  induction hx using IntermediateField.adjoin_induction with
  | mem y hy =>
      rcases hy with rfl | hy
      · exact hj
      · rw [Set.mem_singleton_iff] at hy
        subst hy
        exact hjN
  | algebraMap a => exact hconst a
  | add y z hy hz ihy ihz => convert hadd ⟨y, hy⟩ ⟨z, hz⟩ ihy ihz using 1 <;> try first | with_reducible_and_instances rfl | rfl
  | inv y hy ih => convert hinv ⟨y, hy⟩ ih using 1 <;> try first | with_reducible_and_instances rfl | rfl
  | mul y z hy hz ihy ihz => convert hmul ⟨y, hy⟩ ⟨z, hz⟩ ihy ihz using 1 <;> try first | with_reducible_and_instances rfl | rfl

end Induction

section Generation

variable {K K' : Type*} [Field K] [Field K'] [Algebra K K'] (N : ℕ) [NeZero N]
variable [Algebra ↥(modularFunctionFieldC K N) ↥(modularFunctionFieldC K' N)]
variable (hι : ∀ x : ↥(modularFunctionFieldC K N),
  algebraMap ↥(modularFunctionFieldC K N) ↥(modularFunctionFieldC K' N) x = fcMap (algebraMap K K') N x)
include hι

private theorem adjoin_range_eq_top :
    IntermediateField.adjoin K' (Set.range (algebraMap ↥(modularFunctionFieldC K N)
      ↥(modularFunctionFieldC K' N))) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  refine FC_induction N (· ∈ IntermediateField.adjoin K' (Set.range (algebraMap ↥(modularFunctionFieldC K N)
      ↥(modularFunctionFieldC K' N)))) (fun a => IntermediateField.algebraMap_mem _ a) ?_ ?_
    (fun _ _ hx hy => add_mem hx hy) (fun _ hx => inv_mem hx)
    (fun _ _ hx hy => mul_mem hx hy) x
  · apply IntermediateField.subset_adjoin
    exact ⟨⟨jqModC K, jqModC_mem K N⟩, by rw [hι, fcMap_jq]⟩
  · apply IntermediateField.subset_adjoin
    exact ⟨⟨jqNModC K N, jqNModC_mem K N⟩, by rw [hι, fcMap_jqN]⟩

variable [Algebra K ↥(modularFunctionFieldC K' N)] [IsScalarTower K K' ↥(modularFunctionFieldC K' N)]
  [IsScalarTower K ↥(modularFunctionFieldC K N) ↥(modularFunctionFieldC K' N)] [Algebra.IsAlgebraic K K']

private theorem mem_adjoin_range_and_isIntegral (x : ↥(modularFunctionFieldC K' N)) :
    x ∈ Algebra.adjoin ↥(modularFunctionFieldC K N) (Set.range (algebraMap K' ↥(modularFunctionFieldC K' N))) ∧
      IsIntegral ↥(modularFunctionFieldC K N) x := by
  set S := Algebra.adjoin ↥(modularFunctionFieldC K N)
    (Set.range (algebraMap K' ↥(modularFunctionFieldC K' N))) with hSdef

  have hgen : Set.range (algebraMap K' ↥(modularFunctionFieldC K' N))
      ⊆ (integralClosure ↥(modularFunctionFieldC K N) ↥(modularFunctionFieldC K' N) : Set _) := by
    rintro _ ⟨a, rfl⟩
    rw [SetLike.mem_coe, mem_integralClosure_iff]
    have h1 : IsAlgebraic K (algebraMap K' ↥(modularFunctionFieldC K' N) a) :=
      (Algebra.IsAlgebraic.isAlgebraic (R := K) a).algebraMap
    exact isAlgebraic_iff_isIntegral.mp (IsAlgebraic.tower_top (L := ↥(modularFunctionFieldC K N)) h1)
  have hSint : ∀ y ∈ S, IsIntegral ↥(modularFunctionFieldC K N) y := fun y hy =>
    (mem_integralClosure_iff _ _).mp (Algebra.adjoin_le hgen hy)
  have hS : ∀ y, y ∈ S := by
    refine FC_induction N (· ∈ S) ?_ ?_ ?_ (fun _ _ hx hy => add_mem hx hy) ?_
      (fun _ _ hx hy => mul_mem hx hy)
    · intro a
      exact Algebra.subset_adjoin ⟨a, rfl⟩
    · rw [← fcMap_jq (algebraMap K K') N, ← hι]
      exact S.algebraMap_mem _
    · rw [← fcMap_jqN (algebraMap K K') N, ← hι]
      exact S.algebraMap_mem _
    · intro y hy
      have hyint := hSint y hy
      exact Algebra.adjoin_le (Set.singleton_subset_iff.mpr hy) hyint.inv_mem_adjoin
  exact ⟨hS x, hSint x (hS x)⟩

end Generation

section Constants

private theorem mem_range_of_isAlgebraic (K : Type*) [Field K] (N : ℕ) [NeZero N]
    (y : ↥(modularFunctionFieldC K N)) (hy : IsAlgebraic K y) :
    y ∈ (algebraMap K ↥(modularFunctionFieldC K N)).range := by
  have h1 : IsAlgebraic K (y : LaurentSeries K) := hy.algebraMap (A := LaurentSeries K)
  have h2 := LaurentSeries.eq_C_coeff_zero_of_isAlgebraic h1
  refine ⟨(y : LaurentSeries K).coeff 0, ?_⟩
  apply Subtype.ext
  change algebraMap K (LaurentSeries K) ((y : LaurentSeries K).coeff 0) = (y : LaurentSeries K)
  rw [algebraMap_laurentSeries_eq_single]
  conv_rhs => rw [h2]
  rfl

end Constants

section Rationality

variable {q : ℕ} [Fact q.Prime] {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q]

omit [CharP k q] in

private theorem coeff_pow_card_eq (σ : ZMod q →+* k) (t₀ : ↥(modularFunctionFieldC (ZMod q) N)) (n : ℤ) :
    ((fcMap σ N t₀ : ↥(modularFunctionFieldC k N)) : LaurentSeries k).coeff n ^ q
      = ((fcMap σ N t₀ : ↥(modularFunctionFieldC k N)) : LaurentSeries k).coeff n := by
  rw [fcMap_coe, coeffMap_coeff, ← map_pow, ZMod.pow_card]

private theorem arithFrobC_smul_eq_self [PerfectField k] (t : ↥(modularFunctionFieldC k N))
    (ht : ∀ n : ℤ, ((t : LaurentSeries k).coeff n) ^ q = (t : LaurentSeries k).coeff n) :
    arithFrobC q k N • t = t := by
  apply Subtype.ext
  rw [arithFrobC, coe_coeffSemilinearAut_smul]
  ext n
  rw [coeffMap_coeff]
  exact ht n

private theorem fcMap_fcMap {K K' K'' : Type*} [Field K] [Field K'] [Field K''] (σ : K →+* K') (σ' : K' →+* K'')
    (x : ↥(modularFunctionFieldC K N)) : fcMap σ' N (fcMap σ N x) = fcMap (σ'.comp σ) N x :=
  Subtype.ext (coeffMap_coeffMap σ' σ (x : LaurentSeries K))

end Rationality

section NeTop

variable {q : ℕ} [Fact q.Prime] {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] [IsAlgClosed k]
  [DecidableEq k] [Algebra (ZMod q) k]

private theorem comap_ne_top_of_isSupersingularPlace (w : Place k (modularFunctionFieldC k N))
    (hw : IsSupersingularPlace q N k w) (k₀ : IntermediateField (ZMod q) k)
    (hk₀ : ∀ a : k, IsAlgebraic (ZMod q) a → a ∈ k₀) :
    w.toValuationSubring.comap (fcMap (algebraMap ↥k₀ k) N) ≠ ⊤ := by
  obtain ⟨hrat, ⟨hjw, -⟩, hss⟩ := hw
  set α : k := w.evalAt (jGeomGen k N) with hαdef
  have hα2 : α ^ (q ^ 2) = α := ModularCurve.pow_q_sq_eq_self_of_mem_ssJSet q hss
  have hαalg : IsAlgebraic (ZMod q) α := by
    refine ⟨Polynomial.X ^ (q ^ 2) - Polynomial.X, ?_, ?_⟩
    · exact FiniteField.X_pow_card_sub_X_ne_zero (ZMod q) (one_lt_pow₀ (Fact.out : q.Prime).one_lt two_ne_zero)
    · simp [hα2]
  let α₀ : ↥k₀ := ⟨α, hk₀ α hαalg⟩
  let x₁ : ↥(modularFunctionFieldC ↥k₀ N) :=
    ⟨jqModC ↥k₀, jqModC_mem ↥k₀ N⟩ - algebraMap ↥k₀ ↥(modularFunctionFieldC ↥k₀ N) α₀
  have hx₁ : fcMap (algebraMap ↥k₀ k) N x₁ = jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) α := by
    simp only [x₁, map_sub, fcMap_jq, fcMap_algebraMap]
    rfl
  have hmem : jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) α ∈ w.toValuationSubring :=
    sub_mem hjw (w.algebraMap_mem' α)
  have hne : jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) α ≠ 0 := by
    intro h
    apply transcendental_jqModC k
    have h' := congrArg (fun z : ↥(modularFunctionFieldC k N) => (z : LaurentSeries k)) (sub_eq_zero.mp h)
    change jqModC k = ((algebraMap k ↥(modularFunctionFieldC k N) α : ↥(modularFunctionFieldC k N))
      : LaurentSeries k) at h'
    rw [h']
    exact isAlgebraic_algebraMap α

  have hres : residue w.toValuationSubring ⟨_, hmem⟩ = 0 := by
    have h1 := w.algebraMap_evalAt hrat hjw
    have h2 : (⟨_, hmem⟩ : w.toValuationSubring) = ⟨jGeomGen k N, hjw⟩ - algebraMap k w.toValuationSubring α :=
      Subtype.ext (by simp [Place.coe_algebraMap])
    rw [h2, map_sub, ← h1, ← hαdef]
    have h3 : residue w.toValuationSubring (algebraMap k w.toValuationSubring α) = algebraMap k w.ResidueField α :=
      (IsScalarTower.algebraMap_apply k w.toValuationSubring w.ResidueField α).symm
    rw [h3, sub_self]
  have hnonunit : ¬ IsUnit (⟨_, hmem⟩ : w.toValuationSubring) := by
    rw [← mem_nonunits_iff, ← mem_maximalIdeal]
    exact (IsLocalRing.residue_eq_zero_iff _).mp hres
  intro htop
  have hinv : x₁⁻¹ ∈ w.toValuationSubring.comap (fcMap (algebraMap ↥k₀ k) N) := by
    rw [htop]; exact ValuationSubring.mem_top _
  rw [ValuationSubring.mem_comap, map_inv₀, hx₁] at hinv
  exact hnonunit ⟨⟨⟨_, hmem⟩, ⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ hne), Subtype.ext (inv_mul_cancel₀ hne)⟩, rfl⟩

end NeTop

section Downstairs

variable {K K' : Type*} [Field K] [Field K'] [Algebra K K'] [Algebra.IsAlgebraic K K'] [Algebra.IsSeparable K K']
  (N : ℕ) [NeZero N]

private theorem exists_uniformiser_of_algebraic_constants (hN : (N : K) ≠ 0)
    (W : Place K' ↥(modularFunctionFieldC K' N))
    (hjW : fcMap (algebraMap K K') N ⟨jqModC K, jqModC_mem K N⟩ ∈ W.toValuationSubring) :
    ∃ t₀ : ↥(modularFunctionFieldC K N),
      (∀ V' : ValuationSubring ↥(modularFunctionFieldC K N),
        (∀ a : K, algebraMap K ↥(modularFunctionFieldC K N) a ∈ V') →
        (⟨jqModC K, jqModC_mem K N⟩ : ↥(modularFunctionFieldC K N)) ∈ V' → t₀ ∈ V') ∧
      W.ord (fcMap (algebraMap K K') N t₀) = 1 := by
  classical
  let ι₀₁ := fcMap (algebraMap K K') N
  letI instA01 : Algebra ↥(modularFunctionFieldC K N) ↥(modularFunctionFieldC K' N) := ι₀₁.toAlgebra
  letI instA0F1 : Algebra K ↥(modularFunctionFieldC K' N) :=
    ((algebraMap K' ↥(modularFunctionFieldC K' N)).comp (algebraMap K K')).toAlgebra
  haveI instT1 := IsScalarTower.of_algebraMap_eq (R := K) (S := K')
    (A := ↥(modularFunctionFieldC K' N)) (fun _ => rfl)
  haveI instT2 := IsScalarTower.of_algebraMap_eq (R := K) (S := ↥(modularFunctionFieldC K N))
    (A := ↥(modularFunctionFieldC K' N)) (fun a => by
      change _ = ι₀₁ (algebraMap K _ a)
      rw [fcMap_algebraMap]
      rfl)
  have hgen_int := mem_adjoin_range_and_isIntegral (K := K) (K' := K') N (fun _ => rfl)
  haveI hint01 : Algebra.IsIntegral ↥(modularFunctionFieldC K N) ↥(modularFunctionFieldC K' N) :=
    ⟨fun x => (hgen_int x).2⟩
  have hgen1 : Algebra.adjoin ↥(modularFunctionFieldC K N)
      (Set.range (algebraMap K' ↥(modularFunctionFieldC K' N))) = ⊤ :=
    eq_top_iff.mpr (fun x _ => (hgen_int x).1)
  have he : (W.forgetConstants (K := K)).ramificationIndex ↥(modularFunctionFieldC K N) = 1 :=
    AlgebraicCurve.Place.ramificationIndex_forgetConstants_eq_one_of_isConstantFieldExtension hgen1
      (mem_range_of_isAlgebraic K N) W
  let V₀ : Place K ↥(modularFunctionFieldC K N) :=
    (W.forgetConstants (K := K)).restrict ↥(modularFunctionFieldC K N)
  have hordW : ∀ f : ↥(modularFunctionFieldC K N), W.ord (ι₀₁ f) = V₀.ord f := by
    intro f
    have h := (W.forgetConstants (K := K)).ord_restrict (F := ↥(modularFunctionFieldC K N)) f
    rw [he] at h
    first | exact h | simpa using h | (convert h using 2 <;> first | rfl | (simp; done) | (simp +zetaDelta; done) | (unfold Place.forgetConstants; rfl))
  have hjV₀ : (⟨jqModC K, jqModC_mem K N⟩ : ↥(modularFunctionFieldC K N)) ∈ V₀.toValuationSubring :=
    (ValuationSubring.mem_comap).mpr hjW
  obtain ⟨hfin₀, hsep₀⟩ := finite_and_separable K N hN
  obtain ⟨t₀, ht₀reg, ht₀ord⟩ :=
    @exists_ord_eq_one_of_transcendental K _ _ _ _ _ (transcendental_jq K N) hfin₀ hsep₀ V₀ hjV₀
  exact ⟨t₀, ht₀reg, by rw [hordW]; exact ht₀ord⟩

end Downstairs

section Upstairs

variable {K K' : Type*} [Field K] [Field K'] [Algebra K K'] [IsAlgClosed K] (N : ℕ) [NeZero N]

private theorem ord_fcMap_eq_of_toValuationSubring_eq (hN : (N : K) ≠ 0) (hN' : (N : K') ≠ 0)
    (w : Place K' ↥(modularFunctionFieldC K' N)) (W : Place K ↥(modularFunctionFieldC K N))
    (hW : W.toValuationSubring = w.toValuationSubring.comap (fcMap (algebraMap K K') N))
    (x : ↥(modularFunctionFieldC K N)) : w.ord (fcMap (algebraMap K K') N x) = W.ord x := by
  classical
  let ι₁₂ := fcMap (algebraMap K K') N
  letI instA12 : Algebra ↥(modularFunctionFieldC K N) ↥(modularFunctionFieldC K' N) := ι₁₂.toAlgebra
  letI instAKF2 : Algebra K ↥(modularFunctionFieldC K' N) :=
    ((algebraMap K' ↥(modularFunctionFieldC K' N)).comp (algebraMap K K')).toAlgebra
  haveI instT3 := IsScalarTower.of_algebraMap_eq (R := K) (S := K') (A := ↥(modularFunctionFieldC K' N))
    (fun _ => rfl)
  haveI instT4 := IsScalarTower.of_algebraMap_eq (R := K) (S := ↥(modularFunctionFieldC K N))
    (A := ↥(modularFunctionFieldC K' N)) (fun a => by
      change _ = ι₁₂ (algebraMap K _ a)
      rw [fcMap_algebraMap]
      rfl)
  haveI hcurve : IsCurveOver K ↥(modularFunctionFieldC K N) :=
    ModularCurve.isCurveOver_modularFunctionFieldC_of_perfectField K N
  have hgen2 := adjoin_range_eq_top (K := K) (K' := K') N (fun _ => rfl)
  obtain ⟨P', -, hP'ord, hP'uniq⟩ :=
    AlgebraicCurve.Place.exists_comap_algebraMap_eq_of_constantFieldExtension_of_isAlgClosed
      K ↥(modularFunctionFieldC K N) K' ↥(modularFunctionFieldC K' N)
      (hfg_package K N hN) (hfg_package K' N hN') hgen2 W
  have hwP' : w = P' := hP'uniq w hW.symm
  rw [hwP']
  exact hP'ord x

end Upstairs

end SupersingularUniformiser

open SupersingularUniformiser in
theorem solution
    {q : ℕ} [Fact q.Prime] {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    (hqN : ¬ q ∣ N) (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ ssPlaces q N k) :
    ∃ t : ↥(modularFunctionFieldC k N),
      (∀ n : ℤ, ((t : LaurentSeries k).coeff n) ^ q = (t : LaurentSeries k).coeff n) ∧
      (∀ u : Place k (modularFunctionFieldC k N), IsAffineGeomPlace k N u → t ∈ u.toValuationSubring) ∧
      w.ord t = 1 ∧ (arithFrobC q k N • w).ord t = 1 := by
  classical
  have hw' : IsSupersingularPlace q N k w := hw

  letI : Algebra (ZMod q) k := ZMod.algebra k q
  let k₀ : IntermediateField (ZMod q) k := algebraicClosure (ZMod q) k
  haveI hk₀alg : Algebra.IsAlgebraic (ZMod q) ↥k₀ := algebraicClosure.isAlgebraic (ZMod q) k
  haveI hk₀ac : IsAlgClosed ↥k₀ := (algebraicClosure.isAlgClosure (ZMod q) k).isAlgClosed
  have hNq : (N : ZMod q) ≠ 0 := (CharP.cast_eq_zero_iff (ZMod q) q N).not.mpr hqN
  have hNk : (N : k) ≠ 0 := (CharP.cast_eq_zero_iff k q N).not.mpr hqN
  have hNk₀ : (N : ↥k₀) ≠ 0 := fun h => hNk (by simpa using congrArg (algebraMap ↥k₀ k) h)

  let ι₀₁ := fcMap (algebraMap (ZMod q) ↥k₀) N
  let ι₁₂ := fcMap (algebraMap ↥k₀ k) N

  have hneTop : w.toValuationSubring.comap ι₁₂ ≠ ⊤ :=
    comap_ne_top_of_isSupersingularPlace w hw' k₀ (fun a ha => (mem_algebraicClosure_iff).mpr ha)
  have hWconst : ∀ a : ↥k₀, algebraMap ↥k₀ ↥(modularFunctionFieldC ↥k₀ N) a ∈ w.toValuationSubring.comap ι₁₂ := by
    intro a
    rw [ValuationSubring.mem_comap]
    rw [fcMap_algebraMap]
    exact w.algebraMap_mem' _
  let W : Place ↥k₀ ↥(modularFunctionFieldC ↥k₀ N) :=
    { toValuationSubring := w.toValuationSubring.comap ι₁₂
      algebraMap_mem' := hWconst
      ne_top' := hneTop
      isPrincipalIdealRing' :=
        haveI := (finite_and_separable ↥k₀ N hNk₀).1
        ValuationSubring.isPrincipalIdealRing_of_finiteDimensional_adjoin (K := ↥k₀)
          (⟨jqModC ↥k₀, jqModC_mem ↥k₀ N⟩ : ↥(modularFunctionFieldC ↥k₀ N)) _ hWconst hneTop }

  have hjW : ι₀₁ ⟨jqModC (ZMod q), jqModC_mem (ZMod q) N⟩ ∈ W.toValuationSubring := by
    show _ ∈ w.toValuationSubring.comap ι₁₂
    rw [ValuationSubring.mem_comap]
    rw [fcMap_jq, fcMap_jq]
    exact hw'.2.1.1
  obtain ⟨t₀, ht₀reg, ht₀W⟩ := exists_uniformiser_of_algebraic_constants (K := ZMod q) (K' := ↥k₀) N hNq W hjW

  have hordw : ∀ x : ↥(modularFunctionFieldC ↥k₀ N), w.ord (ι₁₂ x) = W.ord x :=
    ord_fcMap_eq_of_toValuationSubring_eq (K := ↥k₀) (K' := k) N hNk₀ hNk w W rfl

  have h1 : ∀ n : ℤ, ((ι₁₂ (ι₀₁ t₀) : LaurentSeries k).coeff n) ^ q = (ι₁₂ (ι₀₁ t₀) : LaurentSeries k).coeff n := by
    intro n
    have h := coeff_pow_card_eq (N := N) ((algebraMap ↥k₀ k).comp (algebraMap (ZMod q) ↥k₀)) t₀ n
    rwa [← fcMap_fcMap] at h
  refine ⟨ι₁₂ (ι₀₁ t₀), h1, ?_, ?_, ?_⟩
  · intro u hu

    have hk : ∀ a : ZMod q, algebraMap (ZMod q) ↥(modularFunctionFieldC (ZMod q) N) a
        ∈ u.toValuationSubring.comap (ι₁₂.comp ι₀₁) := by
      intro a
      rw [ValuationSubring.mem_comap]
      change ι₁₂ (ι₀₁ (algebraMap (ZMod q) _ a)) ∈ u.toValuationSubring
      rw [fcMap_algebraMap, fcMap_algebraMap]
      exact u.algebraMap_mem' _
    have hj : (⟨jqModC (ZMod q), jqModC_mem (ZMod q) N⟩ : ↥(modularFunctionFieldC (ZMod q) N))
        ∈ u.toValuationSubring.comap (ι₁₂.comp ι₀₁) := by
      rw [ValuationSubring.mem_comap]
      change ι₁₂ (ι₀₁ ⟨jqModC (ZMod q), jqModC_mem (ZMod q) N⟩) ∈ u.toValuationSubring
      rw [fcMap_jq, fcMap_jq]
      exact hu.1
    exact (ValuationSubring.mem_comap).mp (ht₀reg _ hk hj)
  · rw [hordw]
    exact ht₀W
  · have hfix : arithFrobC q k N • ι₁₂ (ι₀₁ t₀) = ι₁₂ (ι₀₁ t₀) := arithFrobC_smul_eq_self _ h1
    calc (arithFrobC q k N • w).ord (ι₁₂ (ι₀₁ t₀))
        = (arithFrobC q k N • w).ord (arithFrobC q k N • ι₁₂ (ι₀₁ t₀)) := by rw [hfix]
      _ = w.ord (ι₁₂ (ι₀₁ t₀)) := SemilinearAut.ord_smul _ _ _
      _ = 1 := by rw [hordw]; exact ht₀W

end

end S_ModularCurve_exists_coeff_pow_eq_and_ord_eq_one_of_mem_ssPlaces
end P2MW
export P2MW.S_ModularCurve_exists_coeff_pow_eq_and_ord_eq_one_of_mem_ssPlaces (solution)
