-- Prove2me | solution 1 for ModularCurve.XOne.isMaximal_asIdeal_of_forall_mem_nonunits_imp_mem_of_exists_not_mem_nonunits
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/a55ce937-02d4-5204-a2ae-2899a9d57f1d

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1

import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOne_isMaximal_asIdeal_of_forall_mem_nonunits_imp_mem_of_exists_not_mem_nonunits
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve.TwoChartIntegralModel

namespace InertNU
variable {F : Type*} [Field F]

theorem mem_nonunits_iff' (A : ValuationSubring F) (x : F) :
    x ∈ A.nonunits ↔ x ∈ A ∧ (x = 0 ∨ x⁻¹ ∉ A) := by
  rw [ValuationSubring.mem_nonunits_iff]
  by_cases hx : x = 0
  · subst hx
    simp [A.zero_mem]
  · constructor
    · intro h
      refine ⟨(A.valuation_le_one_iff x).mp h.le, Or.inr ?_⟩
      intro hinv
      have h1 : A.valuation x⁻¹ ≤ 1 := (A.valuation_le_one_iff _).mpr hinv
      rw [map_inv₀] at h1
      have hx' : A.valuation x ≠ 0 := (map_ne_zero _).mpr hx
      have : 1 ≤ A.valuation x := by
        rwa [inv_le_one₀ (zero_lt_iff.mpr hx')] at h1
      exact absurd h (not_lt.mpr this)
    · rintro ⟨-, h0 | hinv⟩
      · exact absurd h0 hx
      · by_contra hlt
        apply hinv
        rw [← A.valuation_le_one_iff, map_inv₀]
        have hx' : A.valuation x ≠ 0 := (map_ne_zero _).mpr hx
        rw [inv_le_one₀ (zero_lt_iff.mpr hx')]
        exact not_lt.mp hlt
end InertNU

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (hΓle : Γ ≤ CongruenceSubgroup.Gamma1 M)
    (hΓge : CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 p ≤ Γ)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K₁ : IntermediateField L (LaurentSeries L))
    (hK₁ : K₁ = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K₁] [IsScalarTower A L ↥K₁]
    (j : ↥K₁) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})

    (W₀ : ValuationSubring ↥K₁)
    (hW₀ : ∀ f : ↥K₁, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (hSW₀ : ∀ s : ↥(chartAlgFin A (↥K₁) j), (s : ↥K₁) ∈ W₀)

    (y : ↥(XFin A (↥K₁) j))
    (hyϖ : algebraMap A ↥(chartAlgFin A (↥K₁) j) ϖ ∈ y.asIdeal)
    (hy𝔓 : ∀ s : ↥(chartAlgFin A (↥K₁) j), (s : ↥K₁) ∈ W₀.nonunits → s ∈ y.asIdeal)
    (hy₀ : ∃ s : ↥(chartAlgFin A (↥K₁) j), s ∈ y.asIdeal ∧ (s : ↥K₁) ∉ W₀.nonunits) :
    y.asIdeal.IsMaximal := by
  classical

  set B : Subalgebra A ↥K₁ := chartAlgFin A (↥K₁) j with hBdef
  let R₀ : Subalgebra A ↥K₁ := Algebra.adjoin A {j}
  have hle : R₀ ≤ B := adjoin_le_chartAlg A (↥K₁) {j}

  letI algR₀B : Algebra ↥R₀ ↥B := (Subalgebra.inclusion hle).toRingHom.toAlgebra
  have halg : ∀ r : ↥R₀, (algebraMap ↥R₀ ↥B r : ↥K₁) = (r : ↥K₁) := fun _ => rfl
  let val : ↥B →ₐ[↥R₀] ↥K₁ :=
    { B.val.toRingHom with commutes' := fun r => rfl }
  have hval : Function.Injective val := fun a b h => Subtype.ext h
  haveI hint : Algebra.IsIntegral ↥R₀ ↥B := ⟨fun x => by
    have hx : IsIntegral (↥R₀) (x : ↥K₁) := x.2
    exact (isIntegral_algHom_iff val hval).mp hx⟩

  let 𝔶 : Ideal ↥B := y.asIdeal
  haveI h𝔶p : 𝔶.IsPrime := y.isPrime
  let ι : ↥B →+* ↥W₀ :=
    { toFun := fun s => ⟨(s : ↥K₁), hSW₀ s⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let 𝔓₀ : Ideal ↥B := (IsLocalRing.maximalIdeal ↥W₀).comap ι
  haveI h𝔓₀p : 𝔓₀.IsPrime := Ideal.IsPrime.comap ι
  have hmem𝔓₀ : ∀ s : ↥B, s ∈ 𝔓₀ ↔ (s : ↥K₁) ∈ W₀.nonunits := by
    intro s
    rw [Ideal.mem_comap, ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
    exact ⟨fun h => ⟨hSW₀ s, h⟩, fun ⟨_, h⟩ => h⟩
  have h𝔓₀y : 𝔓₀ ≤ 𝔶 := fun s hs => hy𝔓 s ((hmem𝔓₀ s).mp hs)
  obtain ⟨s₀, hs₀y, hs₀W⟩ := hy₀
  have hs₀P : s₀ ∉ 𝔓₀ := fun h => hs₀W ((hmem𝔓₀ s₀).mp h)

  have hAinj : Function.Injective (algebraMap A L) := IsFractionRing.injective A L
  have hcoeA : ∀ a : A, ((algebraMap A ↥B a : ↥B) : ↥K₁) = algebraMap A ↥K₁ a := fun _ => rfl
  have hcoeK : ∀ a : A, ((algebraMap A ↥K₁ a : ↥K₁) : LaurentSeries L) = HahnSeries.C (algebraMap A L a) := by
    intro a
    rw [IsScalarTower.algebraMap_apply A L ↥K₁]
    have h1 : ((algebraMap L ↥K₁ (algebraMap A L a) : ↥K₁) : LaurentSeries L) =
        algebraMap L (LaurentSeries L) (algebraMap A L a) := by
      first
        | rfl
        | exact IntermediateField.coe_algebraMap_apply K₁ _
        | exact (IsScalarTower.algebraMap_apply L ↥K₁ (LaurentSeries L) _).symm
    rw [h1]
    first
      | exact RingHom.congr_fun (HahnSeries.C_eq_algebraMap (Γ := ℤ) (R := L)).symm _
      | (rw [HahnSeries.algebraMap_apply']
         first
           | exact HahnSeries.ofPowerSeries_C _
           | (rw [show algebraMap L (PowerSeries L) (algebraMap A L a) = PowerSeries.C (algebraMap A L a) from
                 (RingHom.congr_fun PowerSeries.C_eq_algebraMap.symm _)]
              exact HahnSeries.ofPowerSeries_C _))
  have hϖ0 : ϖ ≠ 0 := by
    intro h
    have : IsLocalRing.maximalIdeal A = ⊥ := by rw [hϖ, h, Ideal.span_singleton_eq_bot]
    exact IsDiscreteValuationRing.not_a_field A this
  have hϖm : ϖ ∈ IsLocalRing.maximalIdeal A := by rw [hϖ]; exact Ideal.mem_span_singleton_self ϖ
  have hϖP : algebraMap A ↥B ϖ ∈ 𝔓₀ := by
    rw [hmem𝔓₀, hcoeA, InertNU.mem_nonunits_iff']
    refine ⟨hcoeA ϖ ▸ hSW₀ _, Or.inr ?_⟩
    intro hinv
    obtain ⟨x, y', hy', hxy⟩ := (hW₀ _).mp hinv

    have hϖL : algebraMap A L ϖ ≠ 0 := (map_ne_zero_iff _ hAinj).mpr hϖ0
    have hC : ((algebraMap A ↥K₁ ϖ : ↥K₁) : LaurentSeries L) = HahnSeries.C (algebraMap A L ϖ) := hcoeK ϖ
    rw [IntermediateField.coe_inv, hC] at hxy
    have e1 : HahnSeries.ofPowerSeries ℤ L (y'.map (algebraMap A L)) =
        HahnSeries.ofPowerSeries ℤ L ((PowerSeries.C ϖ * x).map (algebraMap A L)) := by
      rw [map_mul, PowerSeries.map_C, map_mul, HahnSeries.ofPowerSeries_C, ← hxy, ← mul_assoc,
        mul_inv_cancel₀ (HahnSeries.C_ne_zero hϖL), one_mul]
    have e2 : y'.map (algebraMap A L) = (PowerSeries.C ϖ * x).map (algebraMap A L) :=
      HahnSeries.ofPowerSeries_injective e1
    have e3 : y' = PowerSeries.C ϖ * x := PowerSeries.map_injective (algebraMap A L) hAinj e2
    apply hy'
    rw [e3, map_mul, PowerSeries.map_C, (IsLocalRing.residue_eq_zero_iff ϖ).mpr hϖm, map_zero, zero_mul]

  have hlt : 𝔓₀.comap (algebraMap ↥R₀ ↥B) < 𝔶.comap (algebraMap ↥R₀ ↥B) :=
    Ideal.comap_lt_comap_of_integral_mem_sdiff h𝔓₀y ⟨hs₀y, hs₀P⟩ (Algebra.IsIntegral.isIntegral s₀)

  have htr : Transcendental A j := ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L K₁ A j hj
  have hinj : Function.Injective (Polynomial.aeval (R := A) j) := transcendental_iff_injective.mp htr
  have hrange : (Polynomial.aeval (R := A) j).range = R₀ := (Algebra.adjoin_singleton_eq_range_aeval A j).symm
  let φ : Polynomial A →+* ↥R₀ :=
    (Subalgebra.inclusion hrange.le).toRingHom.comp (Polynomial.aeval (R := A) j).rangeRestrict.toRingHom
  have hφval : ∀ f : Polynomial A, (φ f : ↥K₁) = Polynomial.aeval j f := fun _ => rfl
  have hφinj : Function.Injective φ := by
    intro f g h
    apply hinj
    have := congrArg (fun r : ↥R₀ => (r : ↥K₁)) h
    simpa only [hφval] using this
  have hφsurj : Function.Surjective φ := by
    intro r
    have hr : (r : ↥K₁) ∈ (Polynomial.aeval (R := A) j).range := hrange.symm ▸ r.2
    obtain ⟨f, hf⟩ := hr
    exact ⟨f, Subtype.ext (by rw [hφval]; exact hf)⟩
  let e : Polynomial A ≃+* ↥R₀ := RingEquiv.ofBijective φ ⟨hφinj, hφsurj⟩

  let 𝔮 : Ideal (Polynomial A) := (𝔶.comap (algebraMap ↥R₀ ↥B)).comap φ
  let 𝔮₀ : Ideal (Polynomial A) := (𝔓₀.comap (algebraMap ↥R₀ ↥B)).comap φ
  haveI h𝔮p : 𝔮.IsPrime := Ideal.IsPrime.comap φ
  have hlt' : 𝔮₀ < 𝔮 := by
    refine lt_of_le_of_ne (Ideal.comap_mono hlt.le) ?_
    intro h
    apply hlt.ne
    have := congrArg (Ideal.map φ) h
    rwa [Ideal.map_comap_of_surjective φ hφsurj, Ideal.map_comap_of_surjective φ hφsurj] at this
  have hCϖ : Polynomial.C ϖ ∈ 𝔮₀ := by
    show algebraMap ↥R₀ ↥B (φ (Polynomial.C ϖ)) ∈ 𝔓₀
    have : algebraMap ↥R₀ ↥B (φ (Polynomial.C ϖ)) = algebraMap A ↥B ϖ := by
      apply Subtype.ext
      rw [halg, hφval, Polynomial.aeval_C, hcoeA]
    rw [this]
    exact hϖP

  let ψ : Polynomial A →+* Polynomial (IsLocalRing.ResidueField A) :=
    Polynomial.mapRingHom (IsLocalRing.residue A)
  have hψsurj : Function.Surjective ψ := Polynomial.map_surjective _ IsLocalRing.residue_surjective
  have hkerψ : RingHom.ker ψ ≤ 𝔮₀ := by
    rw [Polynomial.ker_mapRingHom, IsLocalRing.ker_residue, hϖ, Ideal.map_span, Set.image_singleton,
      Ideal.span_singleton_le_iff_mem]
    exact hCϖ
  have hker𝔮 : RingHom.ker ψ ≤ 𝔮 := hkerψ.trans hlt'.le
  haveI h𝔮ψ : (𝔮.map ψ).IsPrime := Ideal.map_isPrime_of_surjective hψsurj hker𝔮
  have hne : 𝔮.map ψ ≠ ⊥ := by
    intro h0
    have h𝔮le : 𝔮 ≤ RingHom.ker ψ := by
      intro f hf
      rw [RingHom.mem_ker]
      have : ψ f ∈ 𝔮.map ψ := Ideal.mem_map_of_mem ψ hf
      rwa [h0, Ideal.mem_bot] at this
    exact (lt_irrefl 𝔮) (lt_of_le_of_lt (h𝔮le.trans hkerψ) hlt')
  haveI h𝔮ψm : (𝔮.map ψ).IsMaximal := IsPrime.to_maximal_ideal hne
  have h𝔮m : 𝔮.IsMaximal := by
    have := Ideal.comap_isMaximal_of_surjective ψ hψsurj (K := 𝔮.map ψ)
    rwa [Ideal.comap_map_of_surjective ψ hψsurj, ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hker𝔮] at this

  have hR₀m : (𝔶.comap (algebraMap ↥R₀ ↥B)).IsMaximal := by
    have h1 : Ideal.map e 𝔮 = 𝔶.comap (algebraMap ↥R₀ ↥B) := Ideal.map_comap_of_surjective φ hφsurj _
    rw [← h1]
    exact Ideal.map_isMaximal_of_equiv e
  exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap 𝔶 hR₀m

end S_ModularCurve_XOne_isMaximal_asIdeal_of_forall_mem_nonunits_imp_mem_of_exists_not_mem_nonunits
end P2MW
export P2MW.S_ModularCurve_XOne_isMaximal_asIdeal_of_forall_mem_nonunits_imp_mem_of_exists_not_mem_nonunits (solution)
