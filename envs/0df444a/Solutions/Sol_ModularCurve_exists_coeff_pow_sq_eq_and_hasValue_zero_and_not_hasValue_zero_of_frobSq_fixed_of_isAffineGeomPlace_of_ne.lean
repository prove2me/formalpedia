-- Prove2me | solution 1 for ModularCurve.exists_coeff_pow_sq_eq_and_hasValue_zero_and_not_hasValue_zero_of_frobSq_fixed_of_isAffineGeomPlace_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/b04b7361-ac1a-50e0-9256-07b5b3955f32

import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_AlgebraicCurve_ConstantFieldPullback
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldC_of_perfectField
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_isSeparable_jqNModC_of_natCast_ne_zero
import Theorems.Thm_ModularCurve_finiteDimensional_and_isSeparable_adjoin_jGeomGen_of_isSeparable_jqNModC
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ValuationSubring_isPrincipalIdealRing_of_finiteDimensional_adjoin
import Theorems.Thm_AlgebraicCurve_Place_eq_of_comap_toValuationSubring_eq_of_isRational
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_coeff_pow_sq_eq_and_hasValue_zero_and_not_hasValue_zero_of_frobSq_fixed_of_isAffineGeomPlace_of_ne
p2m_attr_erase "simp" "ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false
noncomputable section

p2m_open "AlgebraicCurve IsLocalRing ModularCurve~transcendental_jq"
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple
open scoped IntermediateField.algebraAdjoinAdjoin

namespace SupersingularSeparation

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

section Separation

variable {q : ℕ} [Fact q.Prime] {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q]

private def frobSqFixed (q : ℕ) [Fact q.Prime] (k : Type*) [Field k] [CharP k q] : Subfield k where
  carrier := {a : k | a ^ (q ^ 2) = a}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [mul_pow, ha, hb]
  one_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [add_pow_char_pow, ha, hb]
  zero_mem' := by
    show (0 : k) ^ (q ^ 2) = 0
    exact zero_pow (pow_ne_zero 2 (Fact.out : q.Prime).ne_zero)
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [neg_eq_zero_sub, sub_pow_char_pow, ha, zero_pow (pow_ne_zero 2 (Fact.out : q.Prime).ne_zero), zero_sub]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [inv_pow, ha]

private theorem mem_frobSqFixed {a : k} : a ∈ frobSqFixed q k ↔ a ^ (q ^ 2) = a := Iff.rfl

private theorem coeff_pow_sq_eq (t₀ : ↥(modularFunctionFieldC ↥(frobSqFixed q k) N)) (n : ℤ) :
    ((fcMap (algebraMap ↥(frobSqFixed q k) k) N t₀ : ↥(modularFunctionFieldC k N)) : LaurentSeries k).coeff n ^ (q ^ 2)
      = ((fcMap (algebraMap ↥(frobSqFixed q k) k) N t₀ : ↥(modularFunctionFieldC k N)) : LaurentSeries k).coeff n := by
  rw [fcMap_coe, coeffMap_coeff, ← map_pow]
  exact congrArg _ (Subtype.ext ((t₀ : LaurentSeries ↥(frobSqFixed q k)).coeff n).2)

private theorem fcMap_jq_sub {α : k} (hα : α ∈ frobSqFixed q k) :
    fcMap (algebraMap ↥(frobSqFixed q k) k) N
        ((⟨jqModC ↥(frobSqFixed q k), jqModC_mem ↥(frobSqFixed q k) N⟩ : ↥(modularFunctionFieldC ↥(frobSqFixed q k) N))
          - algebraMap ↥(frobSqFixed q k) ↥(modularFunctionFieldC ↥(frobSqFixed q k) N) ⟨α, hα⟩)
      = jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) α := by
  rw [map_sub, fcMap_jq, fcMap_algebraMap]
  rfl

private theorem ord_pos_of_hasValue_zero {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) (f : F)
    (hf : f ≠ 0) (h : v.HasValue f (0 : K)) : 0 < v.ord f := by
  obtain ⟨hm, hres⟩ := h
  rw [map_zero] at hres
  rcases (v.ord_nonneg_of_mem hm).lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    obtain ⟨hm', hu⟩ := v.exists_isUnit_of_ord_eq_zero hf heq.symm
    exact (IsLocalRing.residue_ne_zero_iff_isUnit _).2 hu hres

private theorem arithFrobC_sq_smul_eq_self [IsAlgClosed k] (g : ↥(modularFunctionFieldC k N))
    (hg : ∀ n : ℤ, ((g : LaurentSeries k).coeff n ^ q) ^ q = (g : LaurentSeries k).coeff n) :
    arithFrobC q k N • (arithFrobC q k N • g) = g := by
  apply Subtype.ext
  rw [arithFrobC, coe_coeffSemilinearAut_smul, coe_coeffSemilinearAut_smul]
  ext n
  rw [coeffMap_coeff, coeffMap_coeff]
  exact hg n

private theorem arithFrobC_sq_smul_fcMap [IsAlgClosed k] (t₀ : ↥(modularFunctionFieldC ↥(frobSqFixed q k) N)) :
    arithFrobC q k N • (arithFrobC q k N • fcMap (algebraMap ↥(frobSqFixed q k) k) N t₀)
      = fcMap (algebraMap ↥(frobSqFixed q k) k) N t₀ := by
  apply arithFrobC_sq_smul_eq_self
  intro n
  rw [← pow_mul, ← sq]
  exact coeff_pow_sq_eq t₀ n

private theorem arithFrobC_sq_smul_jGeomGen [IsAlgClosed k] :
    arithFrobC q k N • (arithFrobC q k N • jGeomGen k N) = jGeomGen k N := by
  letI : Algebra (ZMod q) k := ZMod.algebra k q
  have hj : jGeomGen k N = fcMap (algebraMap (ZMod q) k) N ⟨jqModC (ZMod q), jqModC_mem (ZMod q) N⟩ :=
    (fcMap_jq (algebraMap (ZMod q) k) N).symm
  apply arithFrobC_sq_smul_eq_self
  intro n
  rw [hj, coeff_pow_card_eq (algebraMap (ZMod q) k) _ n, coeff_pow_card_eq (algebraMap (ZMod q) k) _ n]

private theorem value_mem_frobSqFixed [IsAlgClosed k] {w : Place k ↥(modularFunctionFieldC k N)}
    (hfix : arithFrobC q k N • (arithFrobC q k N • w) = w) {g : ↥(modularFunctionFieldC k N)}
    (hg : arithFrobC q k N • (arithFrobC q k N • g) = g) {a : k} (ha : w.HasValue g a) : a ∈ frobSqFixed q k := by
  have h1 := (ha.smul (arithFrobC q k N)).smul (arithFrobC q k N)
  rw [hfix, hg, baseAut_arithFrobC_apply, baseAut_arithFrobC_apply] at h1
  rw [mem_frobSqFixed, sq, pow_mul]
  exact (ha.unique h1).symm

private theorem isRational_of_isAlgClosed [IsAlgClosed k] (w : Place k ↥(modularFunctionFieldC k N)) :
    w.IsRational := by
  haveI : IsCurveOver k ↥(modularFunctionFieldC k N) := isCurveOver_modularFunctionFieldC_of_perfectField k N
  haveI : Module.Finite k w.ResidueField := IsCurveOver.finiteResidue w
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := w.ResidueField)).2

private theorem exists_jValue_mem_frobSqFixed [IsAlgClosed k] (w : Place k ↥(modularFunctionFieldC k N))
    (hfix : arithFrobC q k N • (arithFrobC q k N • w) = w) (haff : IsAffineGeomPlace k N w) :
    ∃ α : k, α ∈ frobSqFixed q k ∧ w.HasValue (jGeomGen k N) α := by
  obtain ⟨α, hα, -⟩ := w.exists_hasValue_of_surjective (isRational_of_isAlgClosed w) haff.1
  exact ⟨α, value_mem_frobSqFixed hfix arithFrobC_sq_smul_jGeomGen hα, hα⟩

private theorem hasValue_sub_const {K F : Type*} [Field K] [Field F] [Algebra K F]
    {v : AlgebraicCurve.Place K F} {g : F} {a : K} (h : v.HasValue g a) (c : K) :
    v.HasValue (g - algebraMap K F c) (a - c) := by
  obtain ⟨hg, hr⟩ := h
  refine ⟨sub_mem hg (v.algebraMap_mem' c), ?_⟩
  have hx : (⟨g - algebraMap K F c, sub_mem hg (v.algebraMap_mem' c)⟩ : v.toValuationSubring)
      = ⟨g, hg⟩ - algebraMap K v.toValuationSubring c := rfl
  rw [hx, map_sub, hr, v.residue_algebraMap c, map_sub]

private theorem hasValue_sub_algebraMap_zero_iff {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : AlgebraicCurve.Place K F) (g : F) (c : K) :
    v.HasValue (g - algebraMap K F c) (0 : K) ↔ v.HasValue g c := by
  constructor
  · intro h0
    simpa only [map_neg, sub_neg_eq_add, sub_add_cancel, zero_add] using hasValue_sub_const h0 (-c)
  · intro h
    simpa only [sub_self] using hasValue_sub_const h c

private theorem hasValue_zero_of_ord_pos {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : AlgebraicCurve.Place K F) {t : F} (ht : 0 < v.ord t) : v.HasValue t (0 : K) := by
  have ht0 : t ≠ 0 := by
    rintro rfl
    simp at ht
  have hmem : t ∈ v.toValuationSubring := (v.mem_iff_ord_nonneg ht0).mpr ht.le
  have hmax : (⟨t, hmem⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring :=
    (v.mem_maximalIdeal_iff_ord_pos ht0 hmem).mpr ht
  refine ⟨hmem, ?_⟩
  rw [map_zero]
  exact (IsLocalRing.residue_eq_zero_iff _).mpr hmax

private theorem not_hasValue_zero_of_ord_eq_zero {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : AlgebraicCurve.Place K F) {t : F} (ht0 : t ≠ 0) (ht : v.ord t = 0) : ¬ v.HasValue t (0 : K) := by
  intro h
  obtain ⟨hmem, hres⟩ := h
  have hmax : (⟨t, hmem⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring :=
    (IsLocalRing.residue_eq_zero_iff _).mp (by rw [hres, map_zero])
  have hpos := (v.mem_maximalIdeal_iff_ord_pos ht0 hmem).mp hmax
  rw [ht] at hpos
  exact lt_irrefl _ hpos

private theorem ord_pos_iff_of_comap_eq (w : Place k ↥(modularFunctionFieldC k N))
    (V : Place ↥(frobSqFixed q k) ↥(modularFunctionFieldC ↥(frobSqFixed q k) N))
    (hV : V.toValuationSubring = w.toValuationSubring.comap (fcMap (algebraMap ↥(frobSqFixed q k) k) N))
    {t₀ : ↥(modularFunctionFieldC ↥(frobSqFixed q k) N)} (ht0 : t₀ ≠ 0) :
    0 < V.ord t₀ ↔ 0 < w.ord (fcMap (algebraMap ↥(frobSqFixed q k) k) N t₀) := by
  have h1 : 0 < V.ord t₀ ↔ t₀⁻¹ ∉ V.toValuationSubring := by
    rw [V.mem_iff_ord_nonneg (inv_ne_zero ht0), Place.ord_inv]
    omega
  have h2 : 0 < w.ord (fcMap (algebraMap ↥(frobSqFixed q k) k) N t₀) ↔ t₀⁻¹ ∉ V.toValuationSubring := by
    rw [hV, ValuationSubring.mem_comap, map_inv₀,
      w.mem_iff_ord_nonneg (inv_ne_zero ((map_ne_zero (fcMap (algebraMap ↥(frobSqFixed q k) k) N)).mpr ht0)),
      Place.ord_inv]
    omega
  rw [h1, h2]

private theorem ord_eq_zero_of_comap_eq (w : Place k ↥(modularFunctionFieldC k N))
    (V : Place ↥(frobSqFixed q k) ↥(modularFunctionFieldC ↥(frobSqFixed q k) N))
    (hV : V.toValuationSubring = w.toValuationSubring.comap (fcMap (algebraMap ↥(frobSqFixed q k) k) N))
    {t₀ : ↥(modularFunctionFieldC ↥(frobSqFixed q k) N)} (ht0 : t₀ ≠ 0) (ht : V.ord t₀ = 0) :
    w.ord (fcMap (algebraMap ↥(frobSqFixed q k) k) N t₀) = 0 := by
  have h1 : ¬ 0 < w.ord (fcMap (algebraMap ↥(frobSqFixed q k) k) N t₀) := by
    rw [← ord_pos_iff_of_comap_eq w V hV ht0]
    omega
  have h2 : 0 ≤ w.ord (fcMap (algebraMap ↥(frobSqFixed q k) k) N t₀) := by
    have hm : t₀ ∈ V.toValuationSubring := (V.mem_iff_ord_nonneg ht0).mpr (by omega)
    rw [hV, ValuationSubring.mem_comap] at hm
    exact w.ord_nonneg_of_mem hm
  omega

private theorem comap_ne_top (w : Place k ↥(modularFunctionFieldC k N)) {α : k} (hα : α ∈ frobSqFixed q k)
    (hw : w.HasValue (jGeomGen k N) α) :
    w.toValuationSubring.comap (fcMap (algebraMap ↥(frobSqFixed q k) k) N) ≠ ⊤ := by
  intro htop
  have hmem : ((⟨jqModC ↥(frobSqFixed q k), jqModC_mem ↥(frobSqFixed q k) N⟩ :
        ↥(modularFunctionFieldC ↥(frobSqFixed q k) N))
          - algebraMap ↥(frobSqFixed q k) ↥(modularFunctionFieldC ↥(frobSqFixed q k) N) ⟨α, hα⟩)⁻¹
        ∈ w.toValuationSubring.comap (fcMap (algebraMap ↥(frobSqFixed q k) k) N) := by
    rw [htop]
    exact ValuationSubring.mem_top _
  rw [ValuationSubring.mem_comap, map_inv₀, fcMap_jq_sub hα] at hmem
  have hne0 : jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) α ≠ 0 := by
    intro h0
    rw [sub_eq_zero] at h0
    have halg : IsAlgebraic k (jGeomGen k N) := by
      rw [h0]
      exact isAlgebraic_algebraMap α
    exact transcendental_jq k N halg
  have hpos : 0 < w.ord (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) α) :=
    ord_pos_of_hasValue_zero w _ hne0 ((hasValue_sub_algebraMap_zero_iff w _ α).mpr hw)
  have hnn := w.ord_nonneg_of_mem hmem
  rw [Place.ord_inv] at hnn
  omega

private theorem isRational_of_comap_eq [IsAlgClosed k] (w : Place k ↥(modularFunctionFieldC k N))
    (hfix : arithFrobC q k N • (arithFrobC q k N • w) = w)
    (V : Place ↥(frobSqFixed q k) ↥(modularFunctionFieldC ↥(frobSqFixed q k) N))
    (hV : V.toValuationSubring = w.toValuationSubring.comap (fcMap (algebraMap ↥(frobSqFixed q k) k) N)) :
    V.IsRational := by
  intro r
  obtain ⟨⟨f, hf⟩, rfl⟩ := IsLocalRing.residue_surjective (R := V.toValuationSubring) r
  have hfw : fcMap (algebraMap ↥(frobSqFixed q k) k) N f ∈ w.toValuationSubring := by
    have h := hf
    rwa [hV, ValuationSubring.mem_comap] at h
  obtain ⟨a, ha, -⟩ := w.exists_hasValue_of_surjective (isRational_of_isAlgClosed w) hfw
  have ha₂ : a ∈ frobSqFixed q k := value_mem_frobSqFixed hfix (arithFrobC_sq_smul_fcMap f) ha
  refine ⟨⟨a, ha₂⟩, ?_⟩
  have hfa : V.HasValue f ⟨a, ha₂⟩ := by
    by_cases hfa0 : f = algebraMap ↥(frobSqFixed q k) ↥(modularFunctionFieldC ↥(frobSqFixed q k) N) ⟨a, ha₂⟩
    · rw [hfa0]
      exact V.hasValue_algebraMap _
    · rw [← hasValue_sub_algebraMap_zero_iff]
      apply hasValue_zero_of_ord_pos
      rw [ord_pos_iff_of_comap_eq w V hV (sub_ne_zero.mpr hfa0)]
      have hι : fcMap (algebraMap ↥(frobSqFixed q k) k) N
            (f - algebraMap ↥(frobSqFixed q k) ↥(modularFunctionFieldC ↥(frobSqFixed q k) N) ⟨a, ha₂⟩)
          = fcMap (algebraMap ↥(frobSqFixed q k) k) N f - algebraMap k ↥(modularFunctionFieldC k N) a := by
        rw [map_sub, fcMap_algebraMap]
        rfl
      rw [hι]
      refine ord_pos_of_hasValue_zero w _ ?_ ((hasValue_sub_algebraMap_zero_iff w _ a).mpr ha)
      rw [← hι]
      exact (map_ne_zero _).mpr (sub_ne_zero.mpr hfa0)
  exact hfa.residue_eq.symm

end Separation

section Children

private theorem exists_ord_pos_and_ord_eq_zero_of_transcendental_of_ne
    {k F : Type*} [Field k] [Field F] [Algebra k F] (x : F) (hx : Transcendental k x)
    [FiniteDimensional ↥(IntermediateField.adjoin k ({x} : Set F)) F]
    [Algebra.IsSeparable ↥(IntermediateField.adjoin k ({x} : Set F)) F]
    (v v' : Place k F) (hxv : x ∈ v.toValuationSubring) (hxv' : x ∈ v'.toValuationSubring)
    (hne : v ≠ v') :
    ∃ t : F, (∀ V' : ValuationSubring F, (∀ a : k, algebraMap k F a ∈ V') → x ∈ V' → t ∈ V') ∧
      0 < v.ord t ∧ v'.ord t = 0 := by
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
  have hv : ∀ c : ↥(integralClosure ↥(Algebra.adjoin k ({x} : Set F)) F),
      algebraMap _ F c ∈ v.toValuationSubring := fun c =>
    mem_of_isIntegral_adjoin x v.toValuationSubring v.algebraMap_mem' hxv ((mem_integralClosure_iff _ _).mp c.2)
  have hv' : ∀ c : ↥(integralClosure ↥(Algebra.adjoin k ({x} : Set F)) F),
      algebraMap _ F c ∈ v'.toValuationSubring := fun c =>
    mem_of_isIntegral_adjoin x v'.toValuationSubring v'.algebraMap_mem' hxv' ((mem_integralClosure_iff _ _).mp c.2)
  have hnle : ¬ Place.center _ v hv ≤ Place.center _ v' hv' := by
    intro hle
    apply hne
    have hmax : (Place.centerHeightOneSpectrum _ v hv).asIdeal.IsMaximal := inferInstance
    have hntop : (Place.centerHeightOneSpectrum _ v' hv').asIdeal ≠ ⊤ := Ideal.IsPrime.ne_top inferInstance
    have hPQ : Place.centerHeightOneSpectrum _ v hv = Place.centerHeightOneSpectrum _ v' hv' :=
      IsDedekindDomain.HeightOneSpectrum.ext (Ideal.IsMaximal.eq_of_le hmax hntop hle)
    refine Place.ext ?_
    rw [Place.toValuationSubring_eq_of_forall_mem v hv, Place.toValuationSubring_eq_of_forall_mem v' hv', hPQ]
  obtain ⟨c, hcP, hcP'⟩ := SetLike.not_le_iff_exists.mp hnle
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hcP' (zero_mem _)
  refine ⟨algebraMap _ F c,
    fun V' hk hxV' => mem_of_isIntegral_adjoin x V' hk hxV' ((mem_integralClosure_iff _ _).mp c.2),
    (Place.mem_center_iff_ord_pos v hv hc0).mp hcP, le_antisymm ?_ (v'.ord_nonneg_of_mem (hv' c))⟩
  exact not_lt.mp fun h => hcP' ((Place.mem_center_iff_ord_pos v' hv' hc0).mpr h)

end Children

end SupersingularSeparation

open SupersingularSeparation in
theorem solution
    {q : ℕ} [Fact q.Prime] {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] [IsAlgClosed k]
    (hqN : ¬ q ∣ N) (w w' : Place k (modularFunctionFieldC k N))
    (hfix : arithFrobC q k N • (arithFrobC q k N • w) = w) (haff : IsAffineGeomPlace k N w) (hne : w ≠ w') :
    ∃ t : ↥(modularFunctionFieldC k N),
      (∀ n : ℤ, ((t : LaurentSeries k).coeff n) ^ (q ^ 2) = (t : LaurentSeries k).coeff n) ∧
      (∀ u : Place k (modularFunctionFieldC k N), IsAffineGeomPlace k N u → t ∈ u.toValuationSubring) ∧
      w.HasValue t (0 : k) ∧ ¬ w'.HasValue t (0 : k) := by
  classical
  obtain ⟨α, hα, hwα⟩ := exists_jValue_mem_frobSqFixed w hfix haff
  by_cases hw'α : w'.HasValue (jGeomGen k N) α
  ·
    set ι := fcMap (algebraMap ↥(frobSqFixed q k) k) N with hι
    have hNk₂ : (N : ↥(frobSqFixed q k)) ≠ 0 := by
      intro h
      apply (CharP.cast_eq_zero_iff k q N).not.mpr hqN
      simpa using congrArg (algebraMap ↥(frobSqFixed q k) k) h
    have hconst : ∀ (v : Place k ↥(modularFunctionFieldC k N)) (a : ↥(frobSqFixed q k)),
        algebraMap ↥(frobSqFixed q k) ↥(modularFunctionFieldC ↥(frobSqFixed q k) N) a
          ∈ v.toValuationSubring.comap ι := by
      intro v a
      rw [ValuationSubring.mem_comap, fcMap_algebraMap]
      exact v.algebraMap_mem' _
    let mkV : ∀ v : Place k ↥(modularFunctionFieldC k N), v.toValuationSubring.comap ι ≠ ⊤ →
        Place ↥(frobSqFixed q k) ↥(modularFunctionFieldC ↥(frobSqFixed q k) N) :=
      fun v hv =>
        { toValuationSubring := v.toValuationSubring.comap ι
          algebraMap_mem' := hconst v
          ne_top' := hv
          isPrincipalIdealRing' :=
            haveI := (finite_and_separable ↥(frobSqFixed q k) N hNk₂).1
            ValuationSubring.isPrincipalIdealRing_of_finiteDimensional_adjoin (K := ↥(frobSqFixed q k))
              (⟨jqModC ↥(frobSqFixed q k), jqModC_mem ↥(frobSqFixed q k) N⟩ :
                ↥(modularFunctionFieldC ↥(frobSqFixed q k) N)) _ (hconst v) hv }
    let V := mkV w (comap_ne_top w hα hwα)
    let V' := mkV w' (comap_ne_top w' hα hw'α)
    have hjV : (⟨jqModC ↥(frobSqFixed q k), jqModC_mem ↥(frobSqFixed q k) N⟩ :
        ↥(modularFunctionFieldC ↥(frobSqFixed q k) N)) ∈ V.toValuationSubring := by
      show _ ∈ w.toValuationSubring.comap ι
      rw [ValuationSubring.mem_comap, fcMap_jq]
      exact haff.1
    have hjV' : (⟨jqModC ↥(frobSqFixed q k), jqModC_mem ↥(frobSqFixed q k) N⟩ :
        ↥(modularFunctionFieldC ↥(frobSqFixed q k) N)) ∈ V'.toValuationSubring := by
      show _ ∈ w'.toValuationSubring.comap ι
      rw [ValuationSubring.mem_comap, fcMap_jq]
      exact hw'α.mem
    have hVV' : V ≠ V' := by
      intro hEq
      apply hne
      letI instA : Algebra ↥(modularFunctionFieldC ↥(frobSqFixed q k) N) ↥(modularFunctionFieldC k N) := ι.toAlgebra
      letI instB : Algebra ↥(frobSqFixed q k) ↥(modularFunctionFieldC k N) :=
        ((algebraMap k ↥(modularFunctionFieldC k N)).comp (algebraMap ↥(frobSqFixed q k) k)).toAlgebra
      haveI instT1 := IsScalarTower.of_algebraMap_eq (R := ↥(frobSqFixed q k)) (S := k)
        (A := ↥(modularFunctionFieldC k N)) (fun _ => rfl)
      haveI instT2 := IsScalarTower.of_algebraMap_eq (R := ↥(frobSqFixed q k))
        (S := ↥(modularFunctionFieldC ↥(frobSqFixed q k) N)) (A := ↥(modularFunctionFieldC k N)) (fun a => by
        change _ = ι (algebraMap _ _ a)
        rw [fcMap_algebraMap]
        rfl)
      have hgen := adjoin_range_eq_top (K := ↥(frobSqFixed q k)) (K' := k) N (fun _ => rfl)
      exact AlgebraicCurve.Place.eq_of_comap_toValuationSubring_eq_of_isRational
        hgen V (isRational_of_comap_eq w hfix V rfl) w w' rfl
        (by rw [hEq]; rfl)
    obtain ⟨t₀, ht₀reg, ht₀V, ht₀V'⟩ :=
      @exists_ord_pos_and_ord_eq_zero_of_transcendental_of_ne ↥(frobSqFixed q k) _ _ _ _ _
        (transcendental_jq ↥(frobSqFixed q k) N)
        (finite_and_separable ↥(frobSqFixed q k) N hNk₂).1 (finite_and_separable ↥(frobSqFixed q k) N hNk₂).2
        V V' hjV hjV' hVV'
    have ht₀0 : t₀ ≠ 0 := by
      rintro rfl
      simp at ht₀V
    refine ⟨ι t₀, coeff_pow_sq_eq t₀, ?_, ?_, ?_⟩
    · intro u hu
      have hj : (⟨jqModC ↥(frobSqFixed q k), jqModC_mem ↥(frobSqFixed q k) N⟩ :
          ↥(modularFunctionFieldC ↥(frobSqFixed q k) N)) ∈ u.toValuationSubring.comap ι := by
        rw [ValuationSubring.mem_comap, fcMap_jq]
        exact hu.1
      exact (ValuationSubring.mem_comap).mp (ht₀reg _ (hconst u) hj)
    · exact hasValue_zero_of_ord_pos w ((ord_pos_iff_of_comap_eq w V rfl ht₀0).mp ht₀V)
    · exact not_hasValue_zero_of_ord_eq_zero w' ((map_ne_zero ι).mpr ht₀0)
        (ord_eq_zero_of_comap_eq w' V' rfl ht₀0 ht₀V')
  ·
    refine ⟨fcMap (algebraMap ↥(frobSqFixed q k) k) N
        ((⟨jqModC ↥(frobSqFixed q k), jqModC_mem ↥(frobSqFixed q k) N⟩ : ↥(modularFunctionFieldC ↥(frobSqFixed q k) N))
          - algebraMap ↥(frobSqFixed q k) ↥(modularFunctionFieldC ↥(frobSqFixed q k) N) ⟨α, hα⟩),
      coeff_pow_sq_eq _, ?_, ?_, ?_⟩ <;> rw [fcMap_jq_sub hα]
    · intro u hu
      exact sub_mem hu.1 (u.algebraMap_mem' α)
    · exact (hasValue_sub_algebraMap_zero_iff w _ α).mpr hwα
    · intro h
      exact hw'α ((hasValue_sub_algebraMap_zero_iff w' _ α).mp h)

end

end S_ModularCurve_exists_coeff_pow_sq_eq_and_hasValue_zero_and_not_hasValue_zero_of_frobSq_fixed_of_isAffineGeomPlace_of_ne
end P2MW
export P2MW.S_ModularCurve_exists_coeff_pow_sq_eq_and_hasValue_zero_and_not_hasValue_zero_of_frobSq_fixed_of_isAffineGeomPlace_of_ne (solution)
